import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ParticleBySpacetime

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory
open scoped ContDiff

namespace RVM

lemma trace_prod_diagonal {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : (E × F) →ₗ[ℝ] E × F) :
    LinearMap.trace ℝ (E × F) L =
      LinearMap.trace ℝ E ((LinearMap.fst ℝ E F).comp (L.comp (LinearMap.inl ℝ E F))) +
      LinearMap.trace ℝ F ((LinearMap.snd ℝ E F).comp (L.comp (LinearMap.inr ℝ E F))) := by
  have heq : L = (LinearMap.inl ℝ E F).comp ((LinearMap.fst ℝ E F).comp L) +
      (LinearMap.inr ℝ E F).comp ((LinearMap.snd ℝ E F).comp L) := by
    ext z <;> simp
  calc
    _ = LinearMap.trace ℝ (E × F) ((LinearMap.inl ℝ E F).comp ((LinearMap.fst ℝ E F).comp L)) +
        LinearMap.trace ℝ (E × F) ((LinearMap.inr ℝ E F).comp ((LinearMap.snd ℝ E F).comp L)) := by
      conv_lhs => rw [heq, map_add]
    _ = _ := congrArg₂ (· + ·)
      (LinearMap.trace_comp_comm' (LinearMap.inl ℝ E F) ((LinearMap.fst ℝ E F).comp L)).symm
      (LinearMap.trace_comp_comm' (LinearMap.inr ℝ E F) ((LinearMap.snd ℝ E F).comp L)).symm

lemma trace_fderiv_eq_divergence {F : Vec → Vec} {x : Vec} (hF : DifferentiableAt ℝ F x) :
    LinearMap.trace ℝ Vec (fderiv ℝ F x).toLinearMap = divergence F x := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  unfold Matrix.trace divergence spatialPartial
  apply Finset.sum_congr rfl
  intro i _
  have hd := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x hF.hasFDerivAt
  have hd' : fderiv ℝ (fun y => F y i) x = (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F x) := hd.fderiv
  rw [hd']
  simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_coe,PiLp.proj_apply]
  rfl

def lorentzPhase (E B : Vec → Vec) (z : Phase) : Phase :=
  (velocity z.2, E z.1 + cross (velocity z.2) (B z.1))

lemma contDiff_lorentzPhase {E B : Vec → Vec} {k : ℕ∞ω}
    (hE : ContDiff ℝ k E) (hB : ContDiff ℝ k B) : ContDiff ℝ k (lorentzPhase E B) := by
  exact (contDiff_velocity.comp contDiff_snd).prodMk
    ((hE.comp contDiff_fst).add (contDiff_cross.comp
      ((contDiff_velocity.comp contDiff_snd).prodMk (hB.comp contDiff_fst))))

lemma trace_lorentzPhase {E B : Vec → Vec} (hE : Differentiable ℝ E)
    (hB : Differentiable ℝ B) (z : Phase) :
    LinearMap.trace ℝ Phase (fderiv ℝ (lorentzPhase E B) z).toLinearMap = 0 := by
  have hF : DifferentiableAt ℝ (lorentzPhase E B) z := by
    exact (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) z.2 |>.comp z differentiableAt_snd).prodMk
      (((hE z.1).comp z differentiableAt_fst).add
        ((contDiff_cross.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) _).comp z
          ((contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) z.2 |>.comp z differentiableAt_snd).prodMk
            ((hB z.1).comp z differentiableAt_fst))))
  let D := fderiv ℝ (lorentzPhase E B) z
  have hleft : (LinearMap.fst ℝ Vec Vec).comp (D.toLinearMap.comp (LinearMap.inl ℝ Vec Vec)) = 0 := by
    have hd := hF.hasFDerivAt.fst.comp (f := fun x : Vec => (x,z.2)) z.1
      ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))
    have hc : HasFDerivAt (fun _ : Vec => velocity z.2) (0 : Vec →L[ℝ] Vec) z.1 := hasFDerivAt_const _ _
    have hh := hd.unique hc
    exact congrArg ContinuousLinearMap.toLinearMap hh
  have hright : (LinearMap.snd ℝ Vec Vec).comp (D.toLinearMap.comp (LinearMap.inr ℝ Vec Vec)) =
      (fderiv ℝ (fun v => E z.1 + cross (velocity v) (B z.1)) z.2).toLinearMap := by
    have hd := hF.hasFDerivAt.snd.comp (f := fun v : Vec => (z.1,v)) z.2
      ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))
    exact congrArg ContinuousLinearMap.toLinearMap hd.fderiv.symm
  rw [trace_prod_diagonal,hleft,hright,map_zero,zero_add,
    trace_fderiv_eq_divergence ((contDiff_lorentz (E z.1) (B z.1)).differentiable
      (by simp : (1 : ℕ∞ω) ≠ 0) z.2)]
  exact divergence_lorentz z.2 (E z.1) (B z.1)

end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_bounded_ode_on_Icc {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] {f : ℝ × H → H}
    {a b t₀ L : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ (univ : Set H)))
    (hb : ∀ t ∈ Icc a b, ∀ z, ‖f (t,z)‖ ≤ L) (z₀ : H) :
    ∃ α : ℝ → H, α t₀ = z₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f (t,α t)) (Icc a b) t := by
  let R : ℝ≥0 := ⟨L*(b-a),mul_nonneg hL (sub_nonneg.mpr hab)⟩
  have hsub : Icc a b ×ˢ closedBall z₀ (R:ℝ) ⊆ Icc a b ×ˢ (univ : Set H) :=
    prod_mono_right (subset_univ _)
  obtain ⟨K,hK⟩ := (hf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_closedBall z₀ (R:ℝ)))
    (isCompact_Icc.prod (isCompact_closedBall z₀ (R:ℝ)))
  have hpic : IsPicardLindelof (fun t z => f (t,z)) ⟨t₀,ht₀⟩ z₀ R 0 ⟨L,hL⟩ K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      simpa using hK.dist_le_mul (t,z) (show (t,z) ∈ Icc a b ×ˢ closedBall z₀ (R:ℝ) from ⟨ht,hz⟩)
        (t,w) (show (t,w) ∈ Icc a b ×ˢ closedBall z₀ (R:ℝ) from ⟨ht,hw⟩)
    · intro z _
      exact hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,mem_univ z⟩)
    · intro t ht z _
      exact hb t ht z
    · change L * max (b-t₀) (t₀-a) ≤ (R:ℝ)-0
      simp only [sub_zero]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht₀.1]) (by linarith [ht₀.2])) hL
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

def cutLorentz (E B : Field) (χ : Vec → ℝ) (p : ℝ × Phase) : Phase :=
  (velocity p.2.2, χ p.2.1 • (E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))))

lemma cutLorentz_regular {E B : Field} {χ : Vec → ℝ} {T : ℝ}
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hχ : ContDiff ℝ 1 χ) :
    ContDiffOn ℝ 1 (cutLorentz E B χ) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hx : ContDiff ℝ 1 (fun p : ℝ × Phase => (p.1,p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun p : ℝ × Phase => (p.1,p.2.1))
      (Icc 0 T ×ˢ (univ : Set Phase)) fieldHalfSpace := fun _ hp => hp.1.1
  have hu : ContDiff ℝ 1 (fun p : ℝ × Phase => velocity p.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.contDiffOn.prodMk
    ((hχ.comp (contDiff_fst.comp contDiff_snd)).contDiffOn.smul
      ((hE.comp hx.contDiffOn hm).add
        (contDiff_cross.contDiffOn.comp (hu.contDiffOn.prodMk (hB.comp hx.contDiffOn hm))
          (mapsTo_univ _ _))))

lemma cutLorentz_bounded {E B : Field} {T : ℝ} (_hT : 0 ≤ T) {x₀ : Vec}
    (hE : ContinuousOn E fieldHalfSpace) (hB : ContinuousOn B fieldHalfSpace)
    (χ : ContDiffBump x₀) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc 0 T, ∀ z, ‖cutLorentz E B χ (t,z)‖ ≤ L := by
  have hsub : Icc 0 T ×ˢ closedBall x₀ χ.rOut ⊆ fieldHalfSpace := fun _ hp => hp.1.1
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ χ.rOut)).bddAbove_image
    ((hE.norm.add hB.norm).mono hsub)
  refine ⟨max 1 M, (zero_le_one.trans (le_max_left _ _)),?_⟩
  intro t ht z
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_velocity_lt_one z.2).le.trans (le_max_left _ _)
  change ‖χ z.1 • (E (t,z.1)+cross (velocity z.2) (B (t,z.1)))‖ ≤ max 1 M
  by_cases hχ : χ z.1 = 0
  · simp only [hχ,zero_smul,norm_zero]
    exact zero_le_one.trans (le_max_left _ _)
  have hz : z.1 ∈ closedBall x₀ χ.rOut := ball_subset_closedBall (by
    rw [← χ.support_eq]
    exact hχ)
  calc
    _ = χ z.1 * ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ := by
      rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖E (t,z.1)‖+‖B (t,z.1)‖ := by
      have hc : ‖cross (velocity z.2) (B (t,z.1))‖ ≤ ‖B (t,z.1)‖ :=
        (norm_cross_le (velocity z.2) (B (t,z.1))).trans
          (mul_le_of_le_one_left (norm_nonneg (B (t,z.1))) (norm_velocity_lt_one z.2).le)
      exact (norm_add_le (E (t,z.1)) (cross (velocity z.2) (B (t,z.1)))).trans
        (add_le_add le_rfl hc)
    _ ≤ M := hM ⟨(t,z.1),⟨ht,hz⟩,rfl⟩
    _ ≤ _ := le_max_right _ _

lemma exists_characteristic_on_slab {E B : Field} {T t₀ : ℝ} (hT : 0 ≤ T)
    (ht₀ : t₀ ∈ Icc 0 T) (hE : ContDiffOn ℝ 1 E fieldHalfSpace)
    (hB : ContDiffOn ℝ 1 B fieldHalfSpace) (x₀ v₀ : Vec) :
    ∃ X V : ℝ → Vec, X t₀=x₀ ∧ V t₀=v₀ ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt X (velocity (V t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt V
        (E (t,X t)+cross (velocity (V t)) (B (t,X t))) (Icc 0 T) t) ∧
      LipschitzOnWith 1 X (Icc 0 T) := by
  let χ : ContDiffBump x₀ := ⟨T+1,T+2,by linarith,by linarith⟩
  obtain ⟨L,hL,hbound⟩ := cutLorentz_bounded hT hE.continuousOn hB.continuousOn χ
  obtain ⟨α,hα₀,hα⟩ := exists_bounded_ode_on_Icc hT ht₀ hL
    (cutLorentz_regular hE hB χ.contDiff) hbound (x₀,v₀)
  have hX : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => (α r).1)
      (velocity (α t).2) (Icc 0 T) t := fun t ht => (hα t ht).fst
  have hLip : LipschitzOnWith 1 (fun r => (α r).1) (Icc 0 T) :=
    (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hX
      (fun t _ => by exact_mod_cast (norm_velocity_lt_one (α t).2).le)
  have hone : ∀ t ∈ Icc 0 T, χ (α t).1=1 := by
    intro t ht
    apply χ.one_of_mem_closedBall
    have hdist := hLip.dist_le_mul t ht t₀ ht₀
    simp only [hα₀,NNReal.coe_one,one_mul] at hdist
    change dist (α t).1 x₀ ≤ T+1
    have hd : dist t t₀ ≤ T := by
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [ht.1,ht.2,ht₀.1,ht₀.2]
    linarith
  refine ⟨(fun r => (α r).1),(fun r => (α r).2),congrArg Prod.fst hα₀,
    congrArg Prod.snd hα₀,hX,?_,hLip⟩
  intro t ht
  have hv : HasDerivWithinAt (fun r => (α r).2)
      (χ (α t).1 • (E (t,(α t).1)+cross (velocity (α t).2) (B (t,(α t).1)))) (Icc 0 T) t :=
    (hα t ht).snd
  simpa only [hone t ht,one_smul] using hv

theorem classical_initial_label {d : Datum} {s : Solution} (hs : Classical d s)
    {t : ℝ} (ht : 0 ≤ t) (z : Phase) :
    ∃ z₀ : Phase, s.f (t,z)=d.f₀ z₀ := by
  obtain ⟨X,V,hX₀,hV₀,hX,hV,_⟩ := exists_characteristic_on_slab ht
    (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩) hs.2.1 hs.2.2.1 z.1 z.2
  have hcX : ContinuousOn X (Icc 0 t) := fun r hr => (hX r hr).continuousWithinAt
  have hcV : ContinuousOn V (Icc 0 t) := fun r hr => (hV r hr).continuousWithinAt
  have he := transport_on_characteristic hs.1 hs.2.2.2.2.2.2.2.1
    le_rfl ht hcX hcV
    (fun r hr => (hX r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
    (fun r hr => (hV r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
  refine ⟨(X 0,V 0),?_⟩
  rw [hX₀,hV₀] at he
  exact he.trans (hs.2.2.2.2.2.2.2.2.1 (X 0,V 0))

theorem classical_particle_bound {d : Datum} {s : Solution}
    (hd : Admissible d) (hs : Classical d s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ z, 0 ≤ s.f (t,z) ∧ s.f (t,z) ≤ C := by
  obtain ⟨C,hC⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro t ht z
  obtain ⟨z₀,hz⟩ := classical_initial_label hs ht z
  refine ⟨hs.2.2.2.1 t ht z,?_⟩
  rw [hz]
  exact (le_abs_self _).trans ((hC z₀).trans (le_max_right _ _))

end RVM

end

end OAI
