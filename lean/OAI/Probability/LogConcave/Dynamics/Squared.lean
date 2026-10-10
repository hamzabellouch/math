import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.TerminalMean

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped Classical

variable {X Ω Γ : Type*} [PseudoMetricSpace X] [SeparableSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] [MeasurableSpace Γ]

theorem exists_countable_quantizer {e : ℝ} (he : 0<e) :
    ∃q : X → ℕ,Measurable q ∧ ∀x,dist x (denseSeq X (q x))<e := by
  have hp : ∀x : X, ∃n,dist x (denseSeq X n)<e :=
    fun x => (denseRange_denseSeq X).exists_dist_lt x he
  refine ⟨fun x => Nat.find (hp x),measurable_find hp ?_,fun x => Nat.find_spec (hp x)⟩
  intro n
  exact (continuous_id.dist continuous_const).measurable measurableSet_Iio

def SquaredAt {d : ℕ} (μ : Measure Ω) (ν : Measure Γ)
    (f : Ω → Point d) (g : Γ → Point d) (B : ℝ) : Prop :=
  ∃κ : Measure (Ω × Γ),IsProbabilityMeasure κ ∧ κ.fst=μ ∧ κ.snd=ν ∧
    Integrable (fun z => ‖f z.1-g z.2‖^2) κ ∧ (∫z,‖f z.1-g z.2‖^2 ∂κ)≤B

theorem measurable_coupling_of_pointwise {d : ℕ}
    (μ : Measure Ω) (ν : Measure Γ) (f : X → Ω → Point d) (g : X → Γ → Point d)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (B : X → ℝ) {Lf Lg e : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (he : 0<e)
    (hfl : ∀x y z,‖f x z-f y z‖≤Lf*dist x y)
    (hgl : ∀x y z,‖g x z-g y z‖≤Lg*dist x y)
    (hc : ∀x,SquaredAt μ ν (f x) (g x) (B x)) :
    ∃q : X → ℕ,Measurable q ∧ (∀x,dist x (denseSeq X (q x))<e) ∧
    ∃K : Kernel X (Ω × Γ),IsMarkovKernel K ∧
      ∀x,(K x).fst=μ ∧ (K x).snd=ν ∧
        Integrable (fun z => ‖f x z.1-g x z.2‖^2) (K x) ∧
        (∫z,‖f x z.1-g x z.2‖^2 ∂K x)≤2*B (denseSeq X (q x))+2*((Lf+Lg)*e)^2 := by
  obtain ⟨q,hq,hqe⟩ := exists_countable_quantizer (X:=X) he
  choose κ hκ hfst hsnd hi hb using (fun n => hc (denseSeq X n))
  let K : Kernel X (Ω × Γ) := ⟨fun x => κ (q x),(measurable_of_countable κ).comp hq⟩
  have : IsMarkovKernel K := ⟨fun x => hκ (q x)⟩
  refine ⟨q,hq,hqe,K,inferInstance,?_⟩
  intro x
  have : IsProbabilityMeasure (K x) := hκ (q x)
  let y := denseSeq X (q x)
  let C := ((Lf+Lg)*e)^2
  have hdom : Integrable (fun z : Ω × Γ => 2*‖f y z.1-g y z.2‖^2+2*C) (K x) :=
    ((hi (q x)).const_mul 2).add (integrable_const _)
  have hp (z : Ω × Γ) : ‖f x z.1-g x z.2‖^2≤2*‖f y z.1-g y z.2‖^2+2*C := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (f x z.1) (f y z.1) (g x z.2)
    have hh := norm_sub_le_norm_sub_add_norm_sub (f y z.1) (g y z.2) (g x z.2)
    rw [norm_sub_rev (g y z.2)] at hh
    have hf' := (hfl x y z.1).trans (mul_le_mul_of_nonneg_left (hqe x).le hLf)
    have hg' := (hgl x y z.2).trans (mul_le_mul_of_nonneg_left (hqe x).le hLg)
    have hn : ‖f x z.1-g x z.2‖≤‖f y z.1-g y z.2‖+(Lf+Lg)*e := by linarith
    have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    dsimp only [C]
    nlinarith [sq_nonneg (‖f y z.1-g y z.2‖-(Lf+Lg)*e)]
  have hm : Measurable (fun z : Ω × Γ => ‖f x z.1-g x z.2‖^2) := by
    exact ((hf.of_uncurry_left.comp measurable_fst).sub
      (hg.of_uncurry_left.comp measurable_snd)).norm.pow_const 2
  have hint := hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs,abs_sq] using hp z))
  refine ⟨hfst (q x),hsnd (q x),hint,(integral_mono hint hdom hp).trans ?_⟩
  change (∫z,2*‖f (denseSeq X (q x)) z.1-g (denseSeq X (q x)) z.2‖^2+2*C ∂κ (q x))≤_
  rw [integral_add ((hi (q x)).const_mul 2) (integrable_const _),integral_const_mul,
    integral_const,probReal_univ,one_smul]
  have hh := hb (q x)
  change 2*(∫z,‖f y z.1-g y z.2‖^2 ∂κ (q x))+2*C≤_
  linarith
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

def lift (ν : Measure Ω) (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) : Measure (Ω × B) :=
  ν ⊗ₘ κ.condKernel.comap T hT

instance lift_probability (ν : Measure Ω) [IsProbabilityMeasure ν]
    (κ : Measure (A × B)) [IsProbabilityMeasure κ] (T : Ω → A) (hT : Measurable T) :
    IsProbabilityMeasure (lift ν κ T hT) := by unfold lift; infer_instance

lemma lift_fst (ν : Measure Ω) [SFinite ν] (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) : (lift ν κ T hT).fst=ν := by
  exact Measure.fst_compProd _ _

theorem lift_map (ν : Measure Ω) [SFinite ν] (κ : Measure (A × B)) [IsFiniteMeasure κ]
    (T : Ω → A) (hT : Measurable T) (hlaw : ν.map T=κ.fst) :
    (lift ν κ T hT).map (fun z => (T z.1,z.2))=κ := by
  calc
    _ = κ.fst ⊗ₘ κ.condKernel := by
      ext s hs
      have hm : Measurable (fun z : Ω × B => (T z.1,z.2)) := by fun_prop
      rw [Measure.map_apply hm hs]
      rw [lift,Measure.compProd_apply (hs.preimage (by fun_prop)),Measure.compProd_apply hs]
      simp only [Kernel.comap_apply]
      rw [←hlaw]
      rw [lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := κ.condKernel) hs) hT]
      rfl
    _ = κ := Measure.disintegrate κ κ.condKernel

lemma lift_integrable (ν : Measure Ω) [SFinite ν]
    (κ : Measure (A × B)) [IsFiniteMeasure κ] (T : Ω → A) (hT : Measurable T)
    (hlaw : ν.map T=κ.fst) (f : A × B → ℝ) (hf : Integrable f κ) :
    Integrable (fun z => f (T z.1,z.2)) (lift ν κ T hT) ∧
      (∫z,f (T z.1,z.2) ∂lift ν κ T hT)=∫z,f z ∂κ := by
  have hm : Measurable (fun z : Ω × B => (T z.1,z.2)) := by fun_prop
  have he := lift_map ν κ T hT hlaw
  have hi : Integrable f ((lift ν κ T hT).map (fun z => (T z.1,z.2))) := by rw [he]; exact hf
  exact ⟨hi.comp_measurable hm,(integral_map hm.aemeasurable hi.aestronglyMeasurable).symm.trans
    (by rw [he])⟩
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function SeedCompiler
open scoped BigOperators

variable {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

theorem absorb_coupling (κ : Measure Ω) [IsProbabilityMeasure κ]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure E)
    (anchor : Ω → A) (noise center : Ω → E)
    (ha : Measurable anchor) (hz : Measurable noise) (hc : Measurable center)
    (hlaw : κ.map (fun w => (anchor w,noise w))=μ.prod (stdGaussian E))
    (x : A → E) (hx : Measurable x) {r D K S B : ℝ}
    (hD : 0<D) (hK : 0≤K) (v : Fin k → ℝ) (hv : (∑i,v i^2)≤D^2)
    (M : E → (Fin k → E) → E) (hm : Measurable (uncurry M))
    (hshift : ShiftInvariant r v M)
    (hLip : ∀x y g,‖M x g-M y g‖≤K*‖x-y‖)
    (Q : A → E → E) (hQ : Measurable (uncurry Q))
    (hci : Integrable (fun w => ‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2) κ)
    (hce : (∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ)≤S)
    (π : Measure ((A × (Fin k → E)) × E)) [IsProbabilityMeasure π]
    (hπ : π.fst=μ.prod (Measure.pi fun _ : Fin k => stdGaussian E))
    (hπnoise : π.map (fun z => (z.1.1,z.2))=μ.prod ν)
    (hbi : Integrable (fun z => ‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2) π)
    (hbe : (∫z,‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2 ∂π)≤B) :
    let a := fun i => v i/(2*D)
    let P := slotTransform (sqrtCoefficient a) a
    ∃Λ : Measure ((Ω × (Fin k → E)) × E),IsProbabilityMeasure Λ ∧
      Λ.fst=κ.prod (Measure.pi fun _ : Fin k => stdGaussian E) ∧
      Λ.map (fun z => (anchor z.1.1,z.2))=μ.prod ν ∧
      Integrable (fun z => ‖M (center z.1.1) (P z.1.2)-Q (anchor z.1.1) z.2‖^2) Λ ∧
      (∫z,‖M (center z.1.1) (P z.1.2)-Q (anchor z.1.1) z.2‖^2 ∂Λ)≤2*K^2*S+2*B := by
  dsimp only
  let a := fun i => v i/(2*D)
  let γ : Measure (Fin k → E) := Measure.pi fun _ => stdGaussian E
  let T : Ω × (Fin k → E) → A × (Fin k → E) := fun z =>
    (anchor z.1,restored (sqrtCoefficient a) a (z.2,noise z.1))
  have hT : Measurable T := by
    exact (ha.comp measurable_fst).prodMk ((restored (sqrtCoefficient a) a).measurable.comp
      (measurable_snd.prodMk (hz.comp measurable_fst)))
  have hTlaw : (κ.prod γ).map T=π.fst := by
    rw [hπ]
    exact restored_from_joint_law κ μ anchor noise ha hz hlaw a
      ((normalized_shift_bound hD v hv).trans (by norm_num))
  let Λ := lift (κ.prod γ) π T hT
  have hΛ : Λ.fst=κ.prod γ := lift_fst _ _ _ _
  have hΛmap := lift_map (κ.prod γ) π T hT hTlaw
  have hC₀ := hci.comp_fst γ
  have hC : Integrable (fun z : (Ω × (Fin k → E)) × E =>
      ‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2) Λ := by
    have h : Integrable (fun z : Ω × (Fin k → E) =>
      ‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2) Λ.fst := by
      rw [hΛ]; exact hC₀
    exact h.comp_measurable measurable_fst
  have hCeq : (∫z : (Ω × (Fin k → E)) × E,
      ‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2 ∂Λ)=
      ∫w,‖center w-(x (anchor w)+(r/(2*D)) • noise w)‖^2 ∂κ := by
    have hmf : Measurable (fun z : Ω × (Fin k → E) =>
      ‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2) := by
      exact ((hc.sub ((hx.comp ha).add (hz.const_smul _))).norm.pow_const 2).comp measurable_fst
    rw [←integral_map measurable_fst.aemeasurable hmf.aestronglyMeasurable]
    change (∫z : Ω × (Fin k → E),‖center z.1-(x (anchor z.1)+(r/(2*D)) • noise z.1)‖^2 ∂Λ.fst)=_
    rw [hΛ,integral_prod _ hC₀]
    simp only [integral_const,probReal_univ,one_smul]
  have hJ := lift_integrable (κ.prod γ) π T hT hTlaw
    (fun z => ‖M (x z.1.1) z.1.2-Q z.1.1 z.2‖^2) hbi
  have hmP : Measurable (slotTransform (sqrtCoefficient a) a : (Fin k → E) → _) := by
    unfold slotTransform slotSum; fun_prop
  have hmeas : Measurable (fun z : (Ω × (Fin k → E)) × E =>
      ‖M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2)-Q (anchor z.1.1) z.2‖^2) := by
    exact ((hm.comp ((hc.comp (measurable_fst.comp measurable_fst)).prodMk
      (hmP.comp (measurable_snd.comp measurable_fst)))).sub
      (hQ.comp ((ha.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))).norm.pow_const 2
  have hbound (z : (Ω × (Fin k → E)) × E) :
      ‖M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2)-Q (anchor z.1.1) z.2‖^2≤
        2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
        2*‖M (x (T z.1).1) (T z.1).2-Q (T z.1).1 z.2‖^2 := by
    have he₀ := hLip (center z.1.1) (x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)
      (slotTransform (sqrtCoefficient a) a z.1.2)
    have heq := absorption_pathwise (D:=D) v M hshift (x (anchor z.1.1)) (sqrtCoefficient a) z.1.2 (noise z.1.1)
    rw [heq] at he₀
    have he := he₀
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (M (center z.1.1) (slotTransform (sqrtCoefficient a) a z.1.2))
      (M (x (T z.1).1) (T z.1).2) (Q (anchor z.1.1) z.2)
    have hp := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (mul_nonneg hK (norm_nonneg _)) (norm_nonneg _))).2
      (ht.trans (add_le_add he (le_refl _)))
    change _≤2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
      2*‖M (x (T z.1).1) (T z.1).2-Q (anchor z.1.1) z.2‖^2
    nlinarith [sq_nonneg (K*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖-
      ‖M (x (T z.1).1) (T z.1).2-Q (anchor z.1.1) z.2‖)]
  have hdom := (hC.const_mul (2*K^2)).add (hJ.1.const_mul 2)
  have hi := hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs,abs_sq,Pi.add_apply] using hbound z))
  refine ⟨Λ,inferInstance,hΛ,?_,hi,(integral_mono hi hdom hbound).trans ?_⟩
  · rw [←hπnoise,←hΛmap,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · change (∫z : (Ω × (Fin k → E)) × E,
        2*K^2*‖center z.1.1-(x (anchor z.1.1)+(r/(2*D)) • noise z.1.1)‖^2+
        2*‖M (x (T z.1).1) (T z.1).2-Q (T z.1).1 z.2‖^2 ∂Λ)≤_
    rw [integral_add (hC.const_mul _) (hJ.1.const_mul _),integral_const_mul,integral_const_mul,hCeq,hJ.2]
    exact add_le_add (mul_le_mul_of_nonneg_left hce (by positivity))
      (mul_le_mul_of_nonneg_left hbe (by norm_num))
end LogConcaveSampling.Coupling

end

end

section

noncomputable section
namespace LogConcaveSampling.Coupling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators NNReal

variable {Ω Γ W : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace W]
  {d : ℕ}

theorem SquaredAt.of_joint (Λ : Measure W) [IsProbabilityMeasure Λ]
    (μ : Measure Ω) (ν : Measure Γ) (T : W → Ω) (U : W → Γ)
    (hT : Measurable T) (hU : Measurable U) (hl : Λ.map T=μ) (hr : Λ.map U=ν)
    (f : Ω → Point d) (g : Γ → Point d) (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hi : Integrable (fun w => ‖f (T w)-g (U w)‖^2) Λ)
    (he : (∫w,‖f (T w)-g (U w)‖^2 ∂Λ)≤B) : SquaredAt μ ν f g B := by
  let J : W → Ω × Γ := fun w => (T w,U w)
  have hJ : Measurable J := hT.prodMk hU
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖^2) := by fun_prop
  refine ⟨Λ.map J,inferInstance,?_,?_,?_,?_⟩
  · change (Λ.map J).map Prod.fst=μ
    rw [Measure.map_map measurable_fst hJ]
    exact hl
  · change (Λ.map J).map Prod.snd=ν
    rw [Measure.map_map measurable_snd hJ]
    exact hr
  · exact (integrable_map_measure hm.aestronglyMeasurable hJ.aemeasurable).mpr hi
  · rw [integral_map hJ.aemeasurable hm.aestronglyMeasurable]
    exact he

lemma SquaredAt.mono {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B C : ℝ} (h : SquaredAt μ ν f g B) (hBC : B≤C) : SquaredAt μ ν f g C := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  exact ⟨κ,hκ,hl,hr,hi,he.trans hBC⟩

lemma SquaredAt.nonneg {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B : ℝ} (h : SquaredAt μ ν f g B) : 0≤B := by
  obtain ⟨κ,_,_,_,_,he⟩ := h
  exact (integral_nonneg fun _ => sq_nonneg _).trans he

lemma SquaredAt.lipschitz {μ : Measure Ω} {ν : Measure Γ}
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (h : SquaredAt μ ν f g B) {e : ℕ} (T : Point d → Point e)
    {K : ℝ≥0} (hT : LipschitzWith K T) :
    SquaredAt μ ν (T ∘ f) (T ∘ g) ((K:ℝ)^2*B) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  have hp (z : Ω × Γ) : ‖T (f z.1)-T (g z.2)‖^2≤(K:ℝ)^2*‖f z.1-g z.2‖^2 := by
    have hh := hT.dist_le_mul (f z.1) (g z.2)
    simp only [dist_eq_norm] at hh
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hm : Measurable (fun z : Ω × Γ => ‖T (f z.1)-T (g z.2)‖^2) := by
    have := hT.continuous.measurable
    fun_prop
  have hdom := hi.const_mul ((K:ℝ)^2)
  have hnew := hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs,abs_sq] using hp z)
  refine ⟨κ,hκ,hl,hr,hnew,(integral_mono hnew hdom hp).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

lemma SquaredAt.reindex {Ω' Γ' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Γ']
    {μ : Measure Ω} {ν : Measure Γ} {f : Ω → Point d} {g : Γ → Point d}
    {B : ℝ} (h : SquaredAt μ ν f g B) (T : Ω → Ω') (U : Γ → Γ')
    (hT : Measurable T) (hU : Measurable U)
    (f' : Ω' → Point d) (g' : Γ' → Point d) (hf' : Measurable f') (hg' : Measurable g')
    (hfe : ∀z,f' (T z)=f z) (hge : ∀z,g' (U z)=g z) :
    SquaredAt (μ.map T) (ν.map U) f' g' B := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := h
  have := hκ
  refine SquaredAt.of_joint κ (μ.map T) (ν.map U) (T ∘ Prod.fst) (U ∘ Prod.snd)
    (hT.comp measurable_fst) (hU.comp measurable_snd) ?_ ?_ f' g' hf' hg' ?_ ?_
  · rw [←Measure.map_map hT measurable_fst]; exact congrArg (Measure.map T) hl
  · rw [←Measure.map_map hU measurable_snd]; exact congrArg (Measure.map U) hr
  · simpa only [Function.comp_apply,hfe,hge] using hi
  · simpa only [Function.comp_apply,hfe,hge] using he

end LogConcaveSampling.Coupling

end

end

end OAI
