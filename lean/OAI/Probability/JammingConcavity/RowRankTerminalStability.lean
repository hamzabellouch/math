import Mathlib
import OAI.Probability.JammingConcavity.RowCalcJet

namespace OAI

/-! Row Rank Terminal Stability. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma row_rank_uniform_gradient (A B C κ Q : ℝ) (hQ : 0<Q)
    (hA : 0≤A) (hC : 0≤C) (hκ : 0≤κ) (hκQ : κ*Q<1) :
    ∃ L : ℝ,0≤L ∧ ∀ u,RowAnalyticTerminal u A B C κ Q →
      ∀ q,RowSmoothProfile Q q → ∀ f,RowClassicalRankSolution u q f →
      ∀ t∈Icc (0:ℝ) 1,∀ x,|deriv (f t) x|≤L*(1+|x|) := by
  obtain ⟨L,hL,hsolve⟩ := row_variance_existence A B C κ Q hQ hA hC hκ hκQ
  refine ⟨L,hL,fun u hu q hq f hf t ht x => ?_⟩
  obtain ⟨m,hm,hmb,hinv,hleft⟩ := rowSmooth_inverse hq
  have hF := rowRank_to_variance hq hm hmb hinv hleft hf
  obtain ⟨G,hG,hbd,huniq,_⟩ := hsolve u hu m hm hmb
  have he : G (q t)=f t := by
    funext x
    simpa only [hleft t ht] using huniq _ hF (q t) (hq.mapsTo ht) x
  simpa only [he] using (hbd (q t) (hq.mapsTo ht) x).2.2.1

lemma row_rank_difference_bound {A B C κ Q L D ε : ℝ} {u v q : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hv : RowAnalyticTerminal v A B C κ Q)
    (hq : RowSmoothProfile Q q) (hL : 0≤L) (hD : 0≤D) (hε : 0≤ε)
    (hqd : ∀ t∈Icc (0:ℝ) 1,deriv q t≤D)
    {f g : ℝ → ℝ → ℝ} (hf : RowClassicalRankSolution u q f) (hg : RowClassicalRankSolution v q g)
    (hfg : ∀ t∈Icc (0:ℝ) 1,∀ x,|deriv (f t) x|≤L*(1+|x|))
    (hgg : ∀ t∈Icc (0:ℝ) 1,∀ x,|deriv (g t) x|≤L*(1+|x|))
    (hterm : ∀ x,|u x-v x|≤ε*(1+x^2)) :
    |f 0 0-g 0 0|≤ε*Real.exp (8*D+8*(D*L)+2) := by
  let U := fun t x => f t x-g t x
  let a := fun t (_ : ℝ) => deriv q t/2
  let b := fun t x => a t x*t*(deriv (f t) x+deriv (g t) x)
  let d := fun t x => -a t x*(deriv (deriv (f t)) x+t*(deriv (f t) x)^2)+
    a t x*(deriv (deriv (g t)) x+t*(deriv (g t) x)^2)
  have hux (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
      HasDerivAt (U t) (deriv (f t) x-deriv (g t) x) x :=
    ((hf.2.2.2.1 t ht).1 x).hasDerivAt.sub ((hg.2.2.2.1 t ht).1 x).hasDerivAt
  have huxx (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
      HasDerivAt (deriv (U t)) (deriv (deriv (f t)) x-deriv (deriv (g t)) x) x := by
    have he : deriv (U t)=fun x => deriv (f t) x-deriv (g t) x := funext (fun x => (hux t ht x).deriv)
    rw [he]
    exact ((hf.2.2.2.1 t ht).2 x).hasDerivAt.sub ((hg.2.2.2.1 t ht).2 x).hasDerivAt
  have hut (t : ℝ) (ht : t∈Ico (0:ℝ) 1) (x : ℝ) :
      HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t := by
    have hft := row_rank_jets_time hQ hu hq hf 0 t ht x
    have hgt := row_rank_jets_time hQ hv hq hg 0 t ht x
    convert hft.sub hgt using 1 <;> first | rfl | (dsimp [U,d,a]; simp only [iteratedDeriv_zero,iteratedDeriv_succ]; ring)
  have ha (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) : 0≤a t x ∧ a t x≤D/2 := by
    dsimp [a]; constructor <;> linarith [hq.2.2.2 t ht,hqd t ht]
  have hb (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : ℝ) : |b t x|≤D*L*(1+|x|) := by
    have hsum : |deriv (f t) x+deriv (g t) x|≤2*L*(1+|x|) :=
      (abs_add_le _ _).trans (by linarith [hfg t ht x,hgg t ht x])
    have hab : 0≤a t x*t ∧ a t x*t≤D/2 := by
      constructor
      · exact mul_nonneg (ha t ht x).1 ht.1
      · exact (mul_le_mul_of_nonneg_left ht.2 (ha t ht x).1).trans (by simpa using (ha t ht x).2)
    dsimp [b]
    rw [abs_mul,abs_of_nonneg hab.1]
    calc
      _ ≤ (D/2)*(2*L*(1+|x|)) := mul_le_mul hab.2 hsum (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hgrowth : Higher.UniformPolynomialGrowth (Icc 0 1) U := by
    obtain ⟨K,hK,hfK⟩ := hf.2.2.2.2.2.2
    obtain ⟨J,hJ,hgJ⟩ := hg.2.2.2.2.2.2
    refine ⟨2,K+J,by positivity,fun t ht x => ?_⟩
    calc
      |U t x| ≤ |f t x|+|g t x| := abs_sub _ _
      _ ≤ K*(1+x^2)+J*(1+x^2) := add_le_add (hfK t ht x).1 (hgJ t ht x).1
      _ ≤ (K+J)*(1+|x|)^2 := by nlinarith [sq_abs x,abs_nonneg x,mul_nonneg hK (abs_nonneg x),mul_nonneg hJ (abs_nonneg x)]
  have hp (t : ℝ) (ht : t∈Ico (0:ℝ) 1) (x : ℝ) :
      |d t x+a t x*deriv (deriv (U t)) x+b t x*deriv (U t) x+(0:ℝ)*U t x|≤(0:ℝ)*(1+x^2)^(0+2) := by
    rw [(hux t ⟨ht.1,ht.2.le⟩ x).deriv,(huxx t ⟨ht.1,ht.2.le⟩ x).deriv]
    have he : d t x+a t x*(deriv (deriv (f t)) x-deriv (deriv (g t)) x)+
        b t x*(deriv (f t) x-deriv (g t) x)+0*U t x=0 := by dsimp [d,b]; ring
    rw [he]; simp
  have hh := VariableDiffusion.backward_polynomial_source_bound (r:=fun _ _ => 0) 0
    (by norm_num : (0:ℝ)<1) (mul_nonneg hD hL) (show 0≤D/2 by positivity)
    (le_refl 0) hε (le_refl 0) (hf.1.sub hg.1)
    (fun t ht => ⟨fun x => (hux t ht x).differentiableAt,fun x => (huxx t ht x).differentiableAt⟩)
    hut ha hb hgrowth (fun _ _ _ => le_refl 0) hp
    (fun x => by
      dsimp [U]; rw [hf.2.2.2.2.2.1,hg.2.2.2.2.2.1]
      exact (hterm x).trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x,sq_nonneg (x^2)]) hε)) 0 (by norm_num) 0
  have he : polynomialBarrier 0 (ε+0) (0+(4*(D/2)*((0:ℕ)+2)^2+4*(D*L)*((0:ℕ)+2)+1)+1) 1 0 0 =
      ε*Real.exp (8*D+8*(D*L)+2) := by
    have hcoef : (0+(4*(D/2)*((0:ℕ)+2)^2+4*(D*L)*((0:ℕ)+2)+1)+1) =
        8*D+8*(D*L)+2 := by norm_num; ring
    simp only [polynomialBarrier,hcoef]
    norm_num
  exact hh.trans_eq he
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma canonicalRank_exists {A B C κ Q : ℝ} {u q : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q) :
    RowClassicalRankSolution u q (canonicalRank u q) := by
  obtain ⟨f,hf,_⟩ := row_rank_existence_unique hQ hu hq
  exact canonicalRank_spec ⟨f,hf⟩

lemma canonicalRank_penalty_bound {A B C κ Q : ℝ} {u q : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q) :
    ∃ M : ℝ,0≤M ∧ ∀ l∈Icc (0:ℝ) 1,
      |canonicalRank (fun z => u z-l*z^2) q 0 0-canonicalRank u q 0 0|≤l*M := by
  have hu0 : RowAnalyticTerminal u (A+1) B (C+2) κ Q := by
    simpa only [zero_mul,sub_zero] using rowTerminal_penalty hu (le_refl 0) (by norm_num : (0:ℝ)≤1)
  obtain ⟨L,hL,hgrad⟩ := row_rank_uniform_gradient (A+1) B (C+2) κ Q hQ hu0.2.1 hu0.2.2.1 hu0.2.2.2.1 hu0.2.2.2.2.1
  obtain ⟨D',hD'⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    (contDiff_infty_iff_deriv.mp hq.1).2.continuous.continuousOn
  let D := max D' 0
  have hD : 0≤D := le_max_right _ _
  have hqd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : deriv q t≤D := by
    have hb : |deriv q t|≤D' := by simpa only [Real.norm_eq_abs] using hD' t ht
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
  refine ⟨Real.exp (8*D+8*(D*L)+2),(Real.exp_pos _).le,fun l hl => ?_⟩
  have hul := rowTerminal_penalty hu hl.1 hl.2
  have hf := canonicalRank_exists hQ hul hq
  have hg := canonicalRank_exists hQ hu0 hq
  apply row_rank_difference_bound hQ hul hu0 hq hL hD hl.1 hqd hf hg
    (hgrad _ hul _ hq _ hf) (hgrad _ hu0 _ hq _ hg)
  intro x
  have he : (u x-l*x^2)-u x=-(l*x^2) := by ring
  rw [he,abs_neg,abs_of_nonneg (mul_nonneg hl.1 (sq_nonneg x))]
  nlinarith [hl.1]

lemma canonicalRank_penalty_limit {A B C κ Q : ℝ} {u q : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q) :
    Tendsto (fun n : ℕ => canonicalRank (fun z => u z-(1/((n:ℝ)+1))*z^2) q 0 0)
      atTop (𝓝 (canonicalRank u q 0 0)) := by
  obtain ⟨M,hM,hbound⟩ := canonicalRank_penalty_bound hQ hu hq
  have hh : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))*M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).mul_const M
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ hh
  intro n
  rw [Real.norm_eq_abs]
  exact hbound _ ⟨by positivity,by apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr; linarith [Nat.cast_nonneg (α:=ℝ) n]⟩
end MicroscopicJamming

 
open Set

namespace MicroscopicJamming
 

def RowSmoothConcavityStatement : Prop :=
  ∀ (u q₀ q₁ : ℝ → ℝ) (A B C κ Q : ℝ), 0<Q →
    RowAnalyticTerminal u A B C κ Q → ConcaveOn ℝ univ u →
    RowSmoothProfile Q q₀ → RowSmoothProfile Q q₁ →
    ∀ θ : ℝ, 0≤θ → θ≤1 →
    ∀ f₀ f₁ fθ : ℝ → ℝ → ℝ,
      RowClassicalRankSolution u q₀ f₀ → RowClassicalRankSolution u q₁ f₁ →
      RowClassicalRankSolution u (fun s => (1-θ)*q₀ s+θ*q₁ s) fθ →
      (1-θ)*f₀ 0 0+θ*f₁ 0 0≤fθ 0 0
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma canonicalRank_chord_concavity {A B C κ Q : ℝ} {u q₀ q₁ : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hc : ConcaveOn ℝ univ u)
    (hq0 : RowSmoothProfile Q q₀) (hq1 : RowSmoothProfile Q q₁) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    (1-θ)*canonicalRank u q₀ 0 0+θ*canonicalRank u q₁ 0 0≤
      canonicalRank u (fun s => q₀ s+θ*(q₁ s-q₀ s)) 0 0 := by
  have hqθ := rowSmooth_chord hq0 hq1 hθ
  have hn (n : ℕ) :
      (1-θ)*canonicalRank (fun z => u z-(1/((n:ℝ)+1))*z^2) q₀ 0 0+
      θ*canonicalRank (fun z => u z-(1/((n:ℝ)+1))*z^2) q₁ 0 0≤
      canonicalRank (fun z => u z-(1/((n:ℝ)+1))*z^2) (fun s => q₀ s+θ*(q₁ s-q₀ s)) 0 0 := by
    let l : ℝ := 1/((n:ℝ)+1)
    have hl : 0<l := by dsimp [l]; positivity
    have hl1 : l≤1 := by
      apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hcon := canonicalRank_chord_concave_strict hQ (rowTerminal_penalty hu hl.le hl1)
      (show 0<2*l by positivity) (rowTerminal_penalty_strict hu hc l) hq0 hq1
    have hh := hcon.2 (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
      (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) (sub_nonneg.mpr hθ.2) hθ.1 (by ring : 1-θ+θ=1)
    have he : (fun s => q₀ s+1*(q₁ s-q₀ s))=q₁ := by funext s; ring
    simpa only [smul_eq_mul,mul_zero,zero_mul,zero_add,mul_one,add_zero,he] using hh
  apply le_of_tendsto_of_tendsto
    (((canonicalRank_penalty_limit hQ hu hq0).const_mul (1-θ)).add
      ((canonicalRank_penalty_limit hQ hu hq1).const_mul θ))
    (canonicalRank_penalty_limit hQ hu hqθ) (Eventually.of_forall hn)

 

theorem rowSmoothConcavity : RowSmoothConcavityStatement := by
  intro u q₀ q₁ A B C κ Q hQ hu hc hq0 hq1 θ hθ0 hθ1 f₀ f₁ fθ hf0 hf1 hfθ
  have hh := canonicalRank_chord_concavity hQ hu hc hq0 hq1 ⟨hθ0,hθ1⟩
  have he : (fun s => q₀ s+θ*(q₁ s-q₀ s))=(fun s => (1-θ)*q₀ s+θ*q₁ s) := by funext s; ring
  have hqθ : RowSmoothProfile Q (fun s => (1-θ)*q₀ s+θ*q₁ s) := by
    rw [←he]; exact rowSmooth_chord hq0 hq1 ⟨hθ0,hθ1⟩
  rw [he] at hh
  rw [canonicalRank_eq hQ hu hq0 hf0 0 (by norm_num) 0,
    canonicalRank_eq hQ hu hq1 hf1 0 (by norm_num) 0,
    canonicalRank_eq hQ hu hqθ hfθ 0 (by norm_num) 0] at hh
  exact hh
end MicroscopicJamming

 

 

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace MicroscopicJamming

 

def rowTiltStep (a T : ℝ) (f : ℝ → ℝ) (x : ℝ) (h : ℝ → ℝ) : ℝ :=
  (∫ z, h (x+Real.sqrt T*z)*Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1) /
  (∫ z, Real.exp (a*f (x+Real.sqrt T*z)) ∂gaussianReal 0 1)

 

def rowDerivativeDepthMoment : List (ℝ × ℝ) → (ℝ → ℝ) → ℕ → ℝ → ℝ
  | rs,u,0,x => (deriv (gaussianRowComposition rs u) x)^2
  | [],u,_+1,x => (deriv u x)^2
  | (a,T)::rs,u,i+1,x => rowTiltStep a T (gaussianRowComposition rs u) x
      (rowDerivativeDepthMoment rs u i)

 

def GaussianDerivativeMartingaleStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
    ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
      (Differentiable ℝ (gaussianRowComposition rs u) ∧
       Differentiable ℝ (deriv (gaussianRowComposition rs u))) ∧
      (∀ a T : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ T → ∀ x,
        deriv (gaussianRowOperator a T (gaussianRowComposition rs u)) x =
          rowTiltStep a T (gaussianRowComposition rs u) x (deriv (gaussianRowComposition rs u))) ∧
      (∀ i x, 0 ≤ rowDerivativeDepthMoment rs u i x ∧ rowDerivativeDepthMoment rs u i x ≤ L^2) ∧
      (∀ x, Monotone (fun i => rowDerivativeDepthMoment rs u i x)) ∧
      (∀ i : Fin rs.length, (rs.get i).2=0 → ∀ x,
        rowDerivativeDepthMoment rs u i.val x=rowDerivativeDepthMoment rs u (i.val+1) x)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def pointCloudMeasure {A : Type*} [MeasurableSpace A] (ω : PointCloud A) : Measure (ℝ × A) :=
  Measure.sum (fun n : ℕ => Measure.sum (fun j : ℕ =>
    if j < (ω n).1 then Measure.dirac ((n:ℝ)+((ω n).2 j).1, ((ω n).2 j).2) else 0))

def PointCloudMeasureMarkingStatement : Prop :=
  ∀ (A : Type) (_ : MeasurableSpace A) (ν : Measure A), IsProbabilityMeasure ν →
  ∀ m : ℝ, 0 < m → m < 1 → ∀ c : A → ℝ,
    Measurable c → (∀ a, 0 < c a) → Integrable (fun a => (c a)^m) ν →
    (∫ a, (c a)^m ∂ν) = 1 →
    IsProbabilityMeasure (pointCloudTilt m c ν) ∧
    (pointCloudLaw ν).map (fun ω => (pointCloudMeasure ω).map
      (fun z : ℝ × A => (z.1/(c z.2)^m,z.2))) =
    (pointCloudLaw (pointCloudTilt m c ν)).map pointCloudMeasure
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma pointCloudTilt_probability {A : Type*} [MeasurableSpace A] (ν : Measure A)
    (m : ℝ) (c : A → ℝ) (hcpos : ∀ a, 0 < c a)
    (hi : Integrable (fun a => (c a)^m) ν) (he : (∫ a, (c a)^m ∂ν) = 1) :
    IsProbabilityMeasure (pointCloudTilt m c ν) := by
  constructor
  rw [pointCloudTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun a => (Real.rpow_pos_of_pos (hcpos a) m).le), he]
  norm_num

lemma marked_intensity_scale {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (m : ℝ) (c : A → ℝ) (hc : Measurable c)
    (hcpos : ∀ a, 0 < c a) (hi : Integrable (fun a => (c a)^m) ν)
    (he : (∫ a, (c a)^m ∂ν) = 1)
    {g : ℝ × A → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g (z.1/(c z.2)^m,z.2) ∂(volume.restrict (Set.Ioi 0)).prod ν) =
      ∫⁻ z, g z ∂(volume.restrict (Set.Ioi 0)).prod (pointCloudTilt m c ν) := by
  let := pointCloudTilt_probability ν m c hcpos hi he
  have hcp : Measurable (fun a => (c a)^m) := by fun_prop
  have hscaled : Measurable (fun z : ℝ × A => g (z.1/(c z.2)^m,z.2)) :=
    hg.comp (measurable_fst.div ((hcp.comp measurable_snd)) |>.prodMk measurable_snd)
  rw [lintegral_prod_symm _ hscaled.aemeasurable,
    lintegral_prod_symm _ hg.aemeasurable]
  rw [pointCloudTilt, lintegral_withDensity_eq_lintegral_mul ν hcp.ennreal_ofReal
    hg.lintegral_prod_left']
  apply lintegral_congr
  intro a
  exact lintegral_Ioi_div (f := fun x => g (x,a))
    (hg.comp (measurable_id.prodMk measurable_const))
    (Real.rpow_pos_of_pos (hcpos a) m)

theorem pointCloudMarking : PointCloudMarkingStatement := by
  intro A mem ν hν m hm hm1 c hc hcpos hi he
  let := hν
  have hprob := pointCloudTilt_probability ν m c hcpos hi he
  refine ⟨hprob, ?_⟩
  let := hprob
  intro f hf
  have hcp : Measurable (fun a => (c a)^m) := by fun_prop
  have hscaled : Measurable (fun z : ℝ × A => f (z.1/(c z.2)^m,z.2)) :=
    hf.comp (measurable_fst.div ((hcp.comp measurable_snd)) |>.prodMk measurable_snd)
  rw [pointCloud_laplace ν hscaled, pointCloud_laplace _ hf]
  congr 1
  exact marked_intensity_scale ν m c hc hcpos hi he
    ((measurable_const.sub (continuous_expNeg.measurable.comp hf)).ennreal_ofReal)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma expNeg_injective : Function.Injective expNeg := by
  intro x y h
  by_cases hx : x = ∞
  · subst x
    by_contra hy
    rw [expNeg_top, expNeg_eq_of_ne_top (Ne.symm hy)] at h
    exact (Real.exp_ne_zero _).symm h
  by_cases hy : y = ∞
  · subst y
    rw [expNeg_top, expNeg_eq_of_ne_top hx] at h
    exact False.elim ((Real.exp_ne_zero _) h)
  rw [expNeg_eq_of_ne_top hx, expNeg_eq_of_ne_top hy] at h
  exact (ENNReal.toReal_eq_toReal_iff' hx hy).mp (neg_injective (Real.exp_injective h))

lemma expNeg_nsmul (n : ℕ) (x : ℝ≥0∞) : expNeg (n • x) = (expNeg x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, expNeg_add, ih, pow_succ]

def laplaceCoordinate {ι : Type*} (i : ι) : C(ι → ℝ≥0∞,ℝ) :=
  ⟨fun x => expNeg (x i), continuous_expNeg.comp (continuous_apply i)⟩

def laplacePolynomial {ι : Type*} : MvPolynomial ι ℝ →ₐ[ℝ] C(ι → ℝ≥0∞,ℝ) :=
  MvPolynomial.aeval laplaceCoordinate

lemma laplacePolynomial_monomial {ι : Type*} (d : ι →₀ ℕ) (r : ℝ) (x : ι → ℝ≥0∞) :
    laplacePolynomial (MvPolynomial.monomial d r) x =
      r * expNeg (d.sum (fun i n => n • x i)) := by
  classical
  rw [laplacePolynomial, MvPolynomial.aeval_monomial]
  simp only [ContinuousMap.mul_apply, algebraMap_apply, Finsupp.prod, Finsupp.sum,
    ContinuousMap.prod_apply, ContinuousMap.pow_apply, laplaceCoordinate, ContinuousMap.coe_mk,
    expNeg_sum, expNeg_nsmul, smul_eq_mul, mul_one]

lemma laplacePolynomial_separates {ι : Type*} :
    (laplacePolynomial (ι := ι)).range.SeparatesPoints := by
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨laplaceCoordinate i, ⟨laplaceCoordinate i, ⟨MvPolynomial.X i, ?_⟩, rfl⟩, ?_⟩
  · exact MvPolynomial.aeval_X _ _
  · exact fun h => hi (expNeg_injective h)

def compactLaplaceIntegral {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] :
    C(X,ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x, f x ∂μ
     map_add' := fun f g => integral_add
       ((BoundedContinuousFunction.mkOfCompact f).integrable μ)
       ((BoundedContinuousFunction.mkOfCompact g).integrable μ)
     map_smul' := fun a f => integral_smul a f } : C(X,ℝ) →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa using (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm μ)

lemma probability_eq_of_laplace {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ≥0∞)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ d : ι →₀ ℕ,
      (∫ x, expNeg (d.sum (fun i n => n • x i)) ∂μ) =
      (∫ x, expNeg (d.sum (fun i n => n • x i)) ∂ν)) : μ = ν := by
  let L : C(ι → ℝ≥0∞,ℝ) →L[ℝ] ℝ := compactLaplaceIntegral μ - compactLaplaceIntegral ν
  have hpoly (p : MvPolynomial ι ℝ) : L (laplacePolynomial p) = 0 := by
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
    | monomial d r =>
      change (∫ x, laplacePolynomial (MvPolynomial.monomial d r) x ∂μ) -
        (∫ x, laplacePolynomial (MvPolynomial.monomial d r) x ∂ν) = 0
      simp_rw [laplacePolynomial_monomial, integral_const_mul, h d]
      exact sub_self _
  have hsub : ((laplacePolynomial (ι := ι)).range : Set C(ι → ℝ≥0∞,ℝ)) ⊆ {f | L f = 0} := by
    rintro _ ⟨p,rfl⟩; exact hpoly p
  have hcls := closure_minimal hsub (isClosed_eq L.continuous continuous_const)
  have htop : closure ((laplacePolynomial (ι := ι)).range : Set C(ι → ℝ≥0∞,ℝ)) = univ := by
    exact congrArg (fun A : Subalgebra ℝ C(ι → ℝ≥0∞,ℝ) => (A : Set C(ι → ℝ≥0∞,ℝ)))
      (ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ laplacePolynomial_separates)
  rw [htop] at hcls
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact sub_eq_zero.mp (hcls (a := f.toContinuousMap) (mem_univ _))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma probability_eq_of_finite_marginals {ι : Type*}
    (μ ν : Measure (ι → ℝ≥0∞)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ I : Finset ι, μ.map I.restrict = ν.map I.restrict) : μ = ν := by
  refine ext_of_generate_finite (measurableCylinders (fun _ : ι => ℝ≥0∞))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ (by simp)
  intro s hs
  obtain ⟨I,S,hS,rfl⟩ := (mem_measurableCylinders _).mp hs
  have hr : Measurable (I.restrict : (ι → ℝ≥0∞) → (I → ℝ≥0∞)) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.val)
  simpa only [Measure.map_apply hr hS, cylinder] using congrArg (fun η => η S) (h I)

def measureEvaluations {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (s : {s : Set A // MeasurableSet s}) : ℝ≥0∞ := μ s

lemma measurable_measureEvaluations {A : Type*} [MeasurableSpace A] :
    Measurable (measureEvaluations (A := A)) :=
  Measurable.of_eval (fun s => Measure.measurable_coe s.prop)

lemma measureEvaluations_comap {A : Type*} [MeasurableSpace A] :
    MeasurableSpace.comap (measureEvaluations (A := A)) inferInstance = (inferInstance : MeasurableSpace (Measure A)) := by
  change MeasurableSpace.comap (fun (μ : Measure A) (s : {s : Set A // MeasurableSet s}) => μ s.val) inferInstance = _
  rw [MeasurableSpace.comap_process_pi]
  exact iSup_subtype

lemma measure_law_eq_of_evaluations {A : Type*} [MeasurableSpace A]
    (μ ν : Measure (Measure A))
    (h : μ.map measureEvaluations = ν.map measureEvaluations) : μ = ν := by
  apply Measure.ext
  intro s hs
  have hs' : MeasurableSet[MeasurableSpace.comap (measureEvaluations (A := A)) inferInstance] s := by
    rw [measureEvaluations_comap]; exact hs
  obtain ⟨t,ht,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs'
  rw [← Measure.map_apply measurable_measureEvaluations ht,
    ← Measure.map_apply measurable_measureEvaluations ht, h]

def finiteMeasureTest {A ι : Type*} [MeasurableSpace A]
    (s : ι → {s : Set A // MeasurableSet s}) (d : ι →₀ ℕ) (a : A) : ℝ≥0∞ :=
  ∑ i ∈ d.support, (d i : ℝ≥0∞) * (s i).val.indicator (fun _ => 1) a

lemma measurable_finiteMeasureTest {A ι : Type*} [MeasurableSpace A]
    (s : ι → {s : Set A // MeasurableSet s}) (d : ι →₀ ℕ) :
    Measurable (finiteMeasureTest s d) :=
  Finset.measurable_fun_sum _ fun i _ =>
    measurable_const.mul (measurable_const.indicator (s i).prop)

lemma integral_finiteMeasureTest {A ι : Type*} [MeasurableSpace A]
    (s : ι → {s : Set A // MeasurableSet s}) (d : ι →₀ ℕ) (η : Measure A) :
    (∫⁻ a, finiteMeasureTest s d a ∂η) = d.sum (fun i n => n • η (s i).val) := by
  classical
  unfold finiteMeasureTest
  rw [lintegral_finsetSum (f := fun (i : ι) (a : A) =>
    (d i : ℝ≥0∞) * (s i).val.indicator (fun _ => (1 : ℝ≥0∞)) a)
    d.support (fun i _ => measurable_const.mul (measurable_const.indicator (s i).prop))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_const_mul _ (measurable_const.indicator (s i).prop),
    lintegral_indicator (s i).prop]
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, nsmul_eq_mul]

lemma probability_finite_measure_evaluations_eq {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ ν : Measure (Measure A)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ f : A → ℝ≥0∞, Measurable f →
      (∫ η, expNeg (∫⁻ a, f a ∂η) ∂μ) = ∫ η, expNeg (∫⁻ a, f a ∂η) ∂ν)
    (s : ι → {s : Set A // MeasurableSet s}) :
    μ.map (fun η i => η (s i).val) = ν.map (fun η i => η (s i).val) := by
  have he : Measurable (fun (η : Measure A) i => η (s i).val) :=
    Measurable.of_eval fun i => Measure.measurable_coe (s i).prop
  have : IsProbabilityMeasure (μ.map (fun η i => η (s i).val)) := inferInstance
  have : IsProbabilityMeasure (ν.map (fun η i => η (s i).val)) := inferInstance
  apply probability_eq_of_laplace
  intro d
  have hk : Measurable (fun x : ι → ℝ≥0∞ => expNeg (d.sum (fun i n => n • x i))) := by
    apply continuous_expNeg.measurable.comp
    simp only [Finsupp.sum, nsmul_eq_mul]
    exact Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _
  rw [integral_map he.aemeasurable hk.aestronglyMeasurable,
    integral_map he.aemeasurable hk.aestronglyMeasurable]
  simpa only [integral_finiteMeasureTest] using h _ (measurable_finiteMeasureTest s d)

lemma probability_measure_law_eq_of_laplace {A : Type*} [MeasurableSpace A]
    (μ ν : Measure (Measure A)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ f : A → ℝ≥0∞, Measurable f →
      (∫ η, expNeg (∫⁻ a, f a ∂η) ∂μ) = ∫ η, expNeg (∫⁻ a, f a ∂η) ∂ν) : μ = ν := by
  classical
  apply measure_law_eq_of_evaluations
  have : IsProbabilityMeasure (μ.map measureEvaluations) := inferInstance
  have : IsProbabilityMeasure (ν.map measureEvaluations) := inferInstance
  apply probability_eq_of_finite_marginals
  intro I
  have hr : Measurable (I.restrict : ({s : Set A // MeasurableSet s} → ℝ≥0∞) → (I → ℝ≥0∞)) :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  rw [Measure.map_map hr measurable_measureEvaluations, Measure.map_map hr measurable_measureEvaluations]
  exact probability_finite_measure_evaluations_eq μ ν h (fun i : I => i.val)
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma measurable_pointCloudMeasure {A : Type*} [MeasurableSpace A] :
    Measurable (pointCloudMeasure (A := A)) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [pointCloudMeasure, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro n
  apply Measurable.tsum
  intro j
  have hx : Measurable (fun ω : PointCloud A =>
      ((n:ℝ)+((ω n).2 j).1, ((ω n).2 j).2)) := by fun_prop
  have hj : MeasurableSet {ω : PointCloud A | j < (ω n).1} := by measurability
  exact (Measure.measurable_coe hs).comp
    ((Measure.measurable_dirac.comp hx).ite hj measurable_const)

lemma lintegral_pointCloudMeasure {A : Type*} [MeasurableSpace A]
    {f : ℝ × A → ℝ≥0∞} (hf : Measurable f) (ω : PointCloud A) :
    (∫⁻ z, f z ∂pointCloudMeasure ω) = pointCloudFunctional f ω := by
  classical
  simp only [pointCloudMeasure, lintegral_sum_measure, pointCloudFunctional]
  apply tsum_congr
  intro n
  have heq (j : ℕ) :
      (∫⁻ z, f z ∂(if j < (ω n).1 then
        Measure.dirac ((n:ℝ)+((ω n).2 j).1, ((ω n).2 j).2) else 0)) =
      if j < (ω n).1 then f ((n:ℝ)+((ω n).2 j).1, ((ω n).2 j).2) else 0 := by
    split_ifs <;> simp [lintegral_dirac' _ hf]
  simp_rw [heq]
  rw [tsum_eq_sum (s := Finset.range (ω n).1) (fun j hj => by
    simp only [Finset.mem_range] at hj; simp [hj])]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  simp [hj]

theorem pointCloudMeasureMarking : PointCloudMeasureMarkingStatement := by
  intro A mem ν hν m hm hm1 c hc hcpos hi he
  let := hν
  have hprob := pointCloudTilt_probability ν m c hcpos hi he
  let := hprob
  refine ⟨hprob, ?_⟩
  have hc' : Measurable (fun a => (c a)^m) := by fun_prop
  let T : ℝ × A → ℝ × A := fun z => (z.1/(c z.2)^m,z.2)
  have hT : Measurable T := (measurable_fst.div (hc'.comp measurable_snd)).prodMk measurable_snd
  have hmT : Measurable (fun ω : PointCloud A => (pointCloudMeasure ω).map T) :=
    (Measure.measurable_map T hT).comp measurable_pointCloudMeasure
  have : IsProbabilityMeasure ((pointCloudLaw ν).map
      (fun ω => (pointCloudMeasure ω).map T)) := inferInstance
  have : IsProbabilityMeasure ((pointCloudLaw (pointCloudTilt m c ν)).map pointCloudMeasure) :=
    inferInstance
  apply probability_measure_law_eq_of_laplace
  intro f hf
  have hk : Measurable (fun η : Measure (ℝ × A) => expNeg (∫⁻ z, f z ∂η)) :=
    continuous_expNeg.measurable.comp (Measure.measurable_lintegral hf)
  rw [integral_map hmT.aemeasurable hk.aestronglyMeasurable,
    integral_map measurable_pointCloudMeasure.aemeasurable hk.aestronglyMeasurable]
  have hfT : Measurable (fun z => f (T z)) := hf.comp hT
  simp_rw [lintegral_map hf hT, lintegral_pointCloudMeasure hf,
    lintegral_pointCloudMeasure hfT]
  exact (pointCloudMarking A mem ν hν m hm hm1 c hc hcpos hi he).2 f hf
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def weightTreeSpace : ℕ → (Σ T : Type, MeasurableSpace T)
  | 0 => ⟨Unit, inferInstanceAs (MeasurableSpace Unit)⟩
  | k+1 => by
    letI := (weightTreeSpace k).2
    exact ⟨Measure (ℝ × (weightTreeSpace k).1), inferInstance⟩

abbrev WeightTree (k : ℕ) := (weightTreeSpace k).1

instance weightTreeMeasurable (k : ℕ) : MeasurableSpace (WeightTree k) := (weightTreeSpace k).2

def weightTreeLaw : (k : ℕ) → Measure (WeightTree k)
  | 0 => Measure.dirac ()
  | k+1 => (pointCloudLaw (weightTreeLaw k)).map pointCloudMeasure

def FamilyCascadeTree (E : Type) : ℕ → Type
  | 0 => Unit
  | k+1 => PointCloud (E × FamilyCascadeTree E k)

instance familyCascadeMeasurable (E : Type) [MeasurableSpace E] :
    (k : ℕ) → MeasurableSpace (FamilyCascadeTree E k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    letI := familyCascadeMeasurable E k
    exact inferInstanceAs (MeasurableSpace (PointCloud (E × FamilyCascadeTree E k)))

def familyCascadeLaw {E : Type} [MeasurableSpace E] :
    (k : ℕ) → (ℕ → Measure E) → Measure (FamilyCascadeTree E k)
  | 0, _ => Measure.dirac ()
  | k+1, ν => pointCloudLaw ((ν 0).prod (familyCascadeLaw k (fun j => ν (j+1))))

def familyRecursion {E : Type} [MeasurableSpace E] [Add E] :
    List ℝ → (ℕ → Measure E) → (E → ℝ) → E → ℝ
  | [], _, u, x => u x
  | m::ms, ν, u, x => (1/m)*Real.log (∫ a, Real.exp
      (m*familyRecursion ms (fun j => ν (j+1)) u (x+a)) ∂ν 0)

def FamilyMomentsFinite {E : Type} [MeasurableSpace E] [Add E] :
    List ℝ → (ℕ → Measure E) → (E → ℝ) → Prop
  | [], _, _ => True
  | m::ms, ν, u =>
      (∀ x, Integrable (fun a => Real.exp
        (m*familyRecursion ms (fun j => ν (j+1)) u (x+a))) (ν 0)) ∧
      FamilyMomentsFinite ms (fun j => ν (j+1)) u

def familyEdgeMultiplier {E : Type} [MeasurableSpace E] [Add E]
    (m : ℝ) (ms : List ℝ) (ν : ℕ → Measure E) (u : E → ℝ) (x a : E) : ℝ :=
  Real.exp (familyRecursion ms (fun j => ν (j+1)) u (x+a) - familyRecursion (m::ms) ν u x)

def transformedWeightTree {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (ℕ → Measure E) → (E → ℝ) → E → FamilyCascadeTree E ms.length → WeightTree ms.length
  | [], _, _, _, _ => ()
  | m::ms, ν, u, x, ω => (pointCloudMeasure ω).map
      (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
        (z.1/(familyEdgeMultiplier m ms ν u x z.2.1)^m,
          transformedWeightTree ms (fun j => ν (j+1)) u (x+z.2.1) z.2.2))

def CascadeGenealogyStatement : Prop :=
  ∀ (E : Type) (_ : MeasurableSpace E) (_ : Add E) (_ : MeasurableAdd₂ E),
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure E, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : E → ℝ, Measurable u → FamilyMomentsFinite ms ν u → ∀ x : E,
    (familyCascadeLaw ms.length ν).map (transformedWeightTree ms ν u x) = weightTreeLaw ms.length
end MicroscopicJamming

end

end OAI
