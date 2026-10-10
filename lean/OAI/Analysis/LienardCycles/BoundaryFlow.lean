import OAI.Analysis.LienardCycles.AxisLimits

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.GlobalODE
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem unique_on_open_interval (V : E → E) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ 1 V U) {f g : ℝ → E} {a b c : ℝ}
    (hc : c ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (V (f t)) t ∧ f t ∈ U)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (V (g t)) t ∧ g t ∈ U)
    (he : f c=g c) : EqOn f g (Ioo a b) := by
  intro t ht
  let A := (a+min t c)/2
  let B := (b+max t c)/2
  have hA : a<A ∧ A < min t c := by dsimp [A]; constructor <;> linarith [lt_min ht.1 hc.1]
  have hB : max t c < B ∧ B<b := by dsimp [B]; constructor <;> linarith [max_lt ht.2 hc.2]
  have hs : Icc A B ⊆ Ioo a b := fun _ h=>⟨hA.1.trans_le h.1,h.2.trans_lt hB.2⟩
  have hfc : ContinuousOn f (Icc A B) := fun x hx=>(hf x (hs hx)).1.continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc A B) := fun x hx=>(hg x (hs hx)).1.continuousAt.continuousWithinAt
  obtain ⟨W,K,L,hK,_,hW⟩ := exists_bounded_lipschitz_cutoff_on V
    ((isCompact_Icc.image_of_continuousOn hfc).union (isCompact_Icc.image_of_continuousOn hgc)) hU
    (by rintro _ (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩); exact (hf x (hs hx)).2; exact (hg x (hs hx)).2) hV
  have hct : c ∈ Ioo A B := ⟨hA.2.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt hB.1⟩
  have heq := ODE_solution_unique_of_mem_Icc (v:=fun _=>W) (s:=fun _=>(Set.univ : Set E))
    (fun _ _=>hK.lipschitzOnWith) hct hfc
    (fun x hx=>by rw [(hW (f x) (Or.inl (mem_image_of_mem _ (Ioo_subset_Icc_self hx)))).self_of_nhds]; exact (hf x (hs (Ioo_subset_Icc_self hx))).1)
    (fun _ _=>mem_univ _) hgc
    (fun x hx=>by rw [(hW (g x) (Or.inr (mem_image_of_mem _ (Ioo_subset_Icc_self hx)))).self_of_nhds]; exact (hg x (hs (Ioo_subset_Icc_self hx))).1)
    (fun _ _=>mem_univ _) he
  exact heq ⟨(hA.2.trans_le (min_le_left _ _)).le,((le_max_left _ _).trans_lt hB.1).le⟩
end QuinticLienard.GlobalODE
namespace QuinticLienard.AxisFlow
open SmoothFlow SmoothFlow.AlgebraicExpr ScaledProfile
noncomputable def X : AlgebraicExpr (ℝ×ℝ) := linear (ContinuousLinearMap.fst ℝ ℝ ℝ)
noncomputable def Y : AlgebraicExpr (ℝ×ℝ) := linear (ContinuousLinearMap.snd ℝ ℝ ℝ)
noncomputable def polynomial (a : Fin 6 → ℝ) : AlgebraicExpr (ℝ×ℝ) :=
  const (a 0)+const (a 1)*X+const (a 2)*X^2+const (a 3)*X^3+const (a 4)*X^4+const (a 5)*X^5
noncomputable def rhs (a : Fin 6 → ℝ) : AlgebraicExpr (ℝ×ℝ) := X*(polynomial a+const (-1)*Y)⁻¹
noncomputable def field (a : Fin 6 → ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (1,z.1/(poly a z.1-z.2))
def domain (a : Fin 6 → ℝ) : Set (ℝ×ℝ) := {z | poly a z.1-z.2≠0}
lemma polynomial_eval (a : Fin 6 → ℝ) (z : ℝ×ℝ) : (polynomial a).eval z=poly a z.1 := by
  simp [polynomial,poly,X]
lemma polynomial_regular (a : Fin 6 → ℝ) (z : ℝ×ℝ) : (polynomial a).RegularAt z := by
  simp [polynomial,X,regular_pow]
lemma rhs_eval (a : Fin 6 → ℝ) (z : ℝ×ℝ) : (rhs a).eval z=z.1/(poly a z.1-z.2) := by
  simp [rhs,X,Y,polynomial_eval,div_eq_mul_inv,sub_eq_add_neg]
lemma rhs_regular (a : Fin 6 → ℝ) {z : ℝ×ℝ} (hz : z ∈ domain a) : (rhs a).RegularAt z := by
  simp only [rhs,regular_mul,regular_inv,regular_add,regular_const,polynomial_regular,true_and]
  simpa [domain,X,Y,polynomial_eval,sub_eq_add_neg] using hz
lemma domain_open (a : Fin 6 → ℝ) : IsOpen (domain a) := by
  apply isOpen_ne_fun
  · unfold poly
    fun_prop
  · fun_prop
lemma field_analytic (a : Fin 6 → ℝ) {z : ℝ×ℝ} (hz : z ∈ domain a) : ContDiffAt ℝ ω (field a) z := by
  have he := (rhs a).eval_analytic (rhs_regular a hz)
  change ContDiffAt ℝ ω (fun q : ℝ×ℝ=>(1,q.1/(poly a q.1-q.2))) z
  simpa only [rhs_eval] using (contDiffAt_const.prodMk he : ContDiffAt ℝ ω (fun q=>((1:ℝ),(rhs a).eval q)) z)
lemma local_flow (a : Fin 6 → ℝ) {z : ℝ×ℝ} (hz : z ∈ domain a) :
    ∃ f : ((ℝ×ℝ)×ℝ) → ℝ×ℝ, ContDiffAt ℝ ω f (z,0) ∧
      ∀ᶠ q in 𝓝 (z,(0:ℝ)), f (q.1,0)=q.1 ∧ HasDerivAt (fun s=>f (q.1,s)) (field a (f q)) q.2 := by
  let I : ℝ →L[ℝ] ℝ×ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  let W : Path (ℝ×ℝ) → Path (ℝ×ℝ) := fun u=>constCLM (1,0)+pathMap I ((rhs a).onPaths u)
  have hp := AlgebraicExpr.path_properties (rhs a) (rhs_regular a hz)
  have hW : ContDiffAt ℝ ω W (constCLM z) := contDiffAt_const.add
    ((pathMap I).contDiff.contDiffAt.comp _ hp.2.1)
  apply exists_analytic_local_flow_eventually W (field a) z _ hW
  filter_upwards [hp.2.2] with u hu s
  simp only [W,ContinuousMap.add_apply,constCLM_apply,pathMap_apply,hu s,rhs_eval]
  simp [I,field]
end QuinticLienard.AxisFlow

end OAI
