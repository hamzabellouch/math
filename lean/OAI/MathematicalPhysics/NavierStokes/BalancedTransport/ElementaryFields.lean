import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Loading
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma literal (q : ℚ) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ _ => (q : ℝ)) := Elementary.literal q

lemma rational {q : ℝ} (hq : RationalConstant q) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ _ => q) := hq.elementary

lemma add (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x + g p t x) := Elementary.add hf hg

lemma mul (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x * g p t x) := Elementary.mul hf hg

lemma sub (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x - g p t x) := Elementary.sub hf hg

lemma neg (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => -f p t x) := Elementary.neg hf

lemma div_rat (q : ℚ) (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => f p t x / (q : ℝ)) := Elementary.div_rat q hf

lemma div_const {q : ℝ} (hq : RationalConstant q) (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => f p t x / q) := by
  obtain ⟨q,rfl⟩ := hq; exact hf.div_rat q

lemma inv (hf : ElementaryScalar f) (n : ℕ) (hn : ∀ p t x, ((n+1:ℕ):ℝ)⁻¹ ≤ f p t x) :
    ElementaryScalar (fun p t x => (f p t x)⁻¹) := Elementary.inv hf n (fun _ => hn _ _ _)

lemma exp (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => Real.exp (f p t x)) := Elementary.exp hf

lemma transition (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => Real.smoothTransition (f p t x)) := Elementary.smoothTransition hf

lemma time : ElementaryScalar (fun _ : Fin d → ℝ => fun t _ => t) := Elementary.coordinate (Fin.castAdd d 0)

lemma space (i : Fin 3) : ElementaryScalar (fun _ : Fin d → ℝ => fun _ x => x i) := Elementary.coordinate (Fin.castAdd d i.succ)

lemma parameter (i : Fin d) : ElementaryScalar (fun p : Fin d → ℝ => fun _ _ => p i) := Elementary.coordinate (Fin.natAdd 4 i)

lemma curve {h : ℝ → ℝ} (hh : ElementaryCurve h) (hf : ElementaryScalar f) :
    ElementaryScalar (fun p t x => h (f p t x)) :=
  Elementary.comp hh (fun z _ => f (fieldParam z) (fieldTime z) (fieldSpace z)) (fun _ => hf)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Field ℝ)
    (hf : ∀ i ∈ s, ElementaryScalar (f i)) : ElementaryScalar (fun p t x => ∑ i ∈ s, f i p t x) :=
  Elementary.sum s _ hf

lemma prod {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Field ℝ)
    (hf : ∀ i ∈ s, ElementaryScalar (f i)) : ElementaryScalar (fun p t x => ∏ i ∈ s, f i p t x) :=
  Elementary.prod s _ hf

lemma congr (hf : ElementaryScalar f) (he : ∀p t x, f p t x = g p t x) : ElementaryScalar g :=
  Elementary.congr hf (fun _ => he _ _ _)

lemma time_differentiable (hf : ElementaryScalar f) (p : Fin d → ℝ) (x : Space) :
    Differentiable ℝ (fun t => f p t x) := by
  intro t
  have hh := (hf.differentiable (fieldArgs p t x)).comp t
    (fieldArgs_time_hasDerivAt p t x).differentiableAt
  simpa only [Function.comp_def,fieldParam_args,fieldTime_args,fieldSpace_args] using hh

lemma space_differentiable (hf : ElementaryScalar f) (p : Fin d → ℝ) (t : ℝ) :
    Differentiable ℝ (f p t) := by
  intro x
  have hh := (hf.differentiable (fieldArgs p t x)).comp x
    (fieldArgs_space_hasFDerivAt p t x).differentiableAt
  simpa only [Function.comp_def,fieldParam_args,fieldTime_args,fieldSpace_args] using hh

end BalancedTransport.Effectivity.ElementaryScalar
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryField
open BalancedTransport.Geometry
variable {d : ℕ} {v w : (Fin d → ℝ) → Velocity}

lemma fullTimeD (hv : ElementaryField v) : ElementaryField (fun p => Geometry.fullTimeD (v p)) := by
  intro i
  apply (ElementaryScalar.fullTimeD (hv i)).congr
  intro p t x
  simp only [Geometry.fullTimeD, deriv_pi (fun k => (hv k).time_differentiable p x t)]

lemma spaceD (hv : ElementaryField v) (i : Fin 3) : ElementaryField (fun p => BalancedTransport.spaceD i (v p)) := by
  intro k
  apply (ElementaryScalar.spaceD (hv k) i).congr
  intro p t x
  simp only [BalancedTransport.spaceD, fderiv_pi (fun j => (hv j).space_differentiable p t x),
    ContinuousLinearMap.pi_apply]

lemma curl (hv : ElementaryField v) : ElementaryField (fun p t => Geometry.curl (v p t)) := by
  intro k
  fin_cases k
  · exact ((hv 2).spaceD 1).sub ((hv 1).spaceD 2)
  · exact ((hv 0).spaceD 2).sub ((hv 2).spaceD 0)
  · exact ((hv 1).spaceD 0).sub ((hv 0).spaceD 1)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Velocity)
    (hf : ∀ i ∈ s, ElementaryField (f i)) : ElementaryField (fun p t x => ∑ i ∈ s, f i p t x) := by
  intro k
  simpa only [Finset.sum_apply] using ElementaryScalar.sum s (fun i p t x => f i p t x k) (fun i hi => hf i hi k)

lemma fullMixedD (hv : ElementaryField v) (a : MultiIndex) :
    ElementaryField (fun p => Geometry.fullMixedD a (v p)) := by
  induction a with
  | nil => exact hv
  | cons i a ih => cases i with
    | none => exact ih.fullTimeD
    | some i => exact ih.spaceD i

end BalancedTransport.Effectivity.ElementaryField
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma elementary_boxCutoff {d : ℕ} {a b : (Fin d → ℝ) → Velocity}
    (ha : ElementaryField a) (hb : ElementaryField b) {η : ℝ} (hη : RationalConstant η) :
    ElementaryScalar (fun p t x => boxCutoff (a p t x) (b p t x) η x) := by
  apply ElementaryScalar.prod Finset.univ
  intro i _
  exact ((((ElementaryScalar.space i).sub (ha i)).add
    ((ElementaryScalar.literal 2).mul (ElementaryScalar.rational hη))).div_const hη).transition.mul
    ((((hb i).add ((ElementaryScalar.literal 2).mul (ElementaryScalar.rational hη))).sub
      (ElementaryScalar.space i)).div_const hη).transition

lemma elementary_affinePotential {d : ℕ} {c v l : (Fin d → ℝ) → Velocity}
    (hc : ElementaryField c) (hv : ElementaryField v) (hl : ElementaryField l) :
    ElementaryField (fun p t x => affinePotential (c p t x) (v p t x) (l p t x) x) := by
  have hh (i j : Fin 3) := ((ElementaryScalar.literal (1/2)).mul
      (((hv i).mul ((ElementaryScalar.space j).sub (hc j))).sub
        ((hv j).mul ((ElementaryScalar.space i).sub (hc i))))).add
    (((ElementaryScalar.literal (1/3)).mul ((hl i).sub (hl j))).mul
      ((ElementaryScalar.space i).sub (hc i)) |>.mul ((ElementaryScalar.space j).sub (hc j)))
  intro k
  fin_cases k
  · simpa [affinePotential] using hh 1 2
  · simpa [affinePotential] using hh 2 0
  · simpa [affinePotential] using hh 0 1

lemma elementary_movingBoxVelocity {d : ℕ} (a b : Space) (ar : ∀i, RationalConstant (a i))
    (br : ∀i, RationalConstant (b i)) {c w : (Fin d → ℝ) → ℝ → Space}
    (hc : ElementaryField (fun p t _ => c p t)) (hw : ElementaryField (fun p t _ => w p t))
    (hn : ∀ i, ∃ n : ℕ, ∀ p t, ((n+1:ℕ):ℝ)⁻¹ ≤ w p t i)
    {η : ℝ} (ηr : RationalConstant η) : ElementaryField (fun p => movingBoxVelocity a b (c p) (w p) η) := by
  have ha : ElementaryField (fun p t _ => lowerEndpoint a (c p) (w p) t) :=
    fun i => (hc i).add ((hw i).mul (ElementaryScalar.rational (ar i)))
  have hb : ElementaryField (fun p t _ => lowerEndpoint b (c p) (w p) t) :=
    fun i => (hc i).add ((hw i).mul (ElementaryScalar.rational (br i)))
  have hl : ElementaryField (fun p t _ => logarithmicRate (w p) t) := by
    intro i
    obtain ⟨n,hn⟩ := hn i
    simpa only [logarithmicRate, fullTimeD, div_eq_mul_inv] using
      (ElementaryScalar.fullTimeD (hw i)).mul ((hw i).inv n (fun p t _ => hn p t))
  have hP := elementary_affinePotential hc hc.fullTimeD hl
  have hχ := elementary_boxCutoff ha hb ηr
  exact ElementaryField.curl (fun i => hχ.mul (hP i))

lemma elementary_loadingVelocity {η : ℝ} (hr : RationalConstant η) :
    ElementaryField (fun p : Fin 3 → ℝ => loadingVelocity p η) := by
  have labelRat : ∀ i, RationalConstant (fixedLabel i) := by
    intro i
    fin_cases i
    · exact RationalConstant.nat 4
    · exact RationalConstant.zero
    · exact RationalConstant.zero
  apply elementary_movingBoxVelocity fixedLabel fixedLabel labelRat labelRat
  · intro i
    simpa only [loadingCenter, loadingSwitch, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      ((((ElementaryScalar.literal 2).mul ElementaryScalar.time).sub
        (ElementaryScalar.literal (1/2))).transition.mul
        ((ElementaryScalar.parameter i).sub (ElementaryScalar.rational (labelRat i))))
  · intro i
    simpa using (ElementaryScalar.literal (d:=3) 1)
  · intro i
    exact ⟨0, by intro p t; norm_num⟩
  · exact hr

end BalancedTransport.Effectivity
end

end OAI
