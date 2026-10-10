import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionComparison

namespace OAI

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V]

omit [Fintype V] in
lemma isClosed_feasible (S : System V E) (b : V → ℝ) : IsClosed (feasible S b) := by
  have he : IsClosed {h : V → ℝ | ∀ e,h (S.left e)-h (S.right e)≤S.cost e} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun e => isClosed_le ((continuous_apply (S.left e)).sub (continuous_apply (S.right e))) continuous_const
  have hp : IsClosed {h : V → ℝ | ∀ x∈S.pins,h x=b x} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq (continuous_apply _) continuous_const
  exact he.inter hp

lemma objective_nonneg (v h : V → ℝ) : 0≤objective v h := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma continuous_objective (v : V → ℝ) : Continuous (objective v) := by
  unfold objective
  fun_prop

lemma coordinate_bound (v h : V → ℝ) (B : ℝ) (hB : 0≤B) (hh : objective v h≤B) (x : V) :
    v x-Real.sqrt B≤h x ∧ h x≤v x+Real.sqrt B := by
  have hx : (h x-v x)^2≤B := (Finset.single_le_sum (fun y (_ : y∈Finset.univ) => sq_nonneg (h y-v y)) (Finset.mem_univ x)).trans hh
  have hs := Real.sq_sqrt hB
  have hn := Real.sqrt_nonneg B
  constructor <;> nlinarith

lemma exists_projection (S : System V E) (b v : V → ℝ) (hne : (feasible S b).Nonempty) :
    ∃ h,IsProjection S b v h := by
  obtain ⟨h₀,hh₀⟩ := hne
  let B := objective v h₀
  let L : V → ℝ := fun x => v x-Real.sqrt B
  let U : V → ℝ := fun x => v x+Real.sqrt B
  have hc : IsCompact (feasible S b ∩ Icc L U) := isCompact_Icc.inter_left (isClosed_feasible S b)
  have hmem (h : V → ℝ) (hh : objective v h≤B) : h∈Icc L U := by
    constructor
    · intro x;exact (coordinate_bound v h B (objective_nonneg v h₀) hh x).1
    · intro x;exact (coordinate_bound v h B (objective_nonneg v h₀) hh x).2
  obtain ⟨h,hh,hmin⟩ := hc.exists_isMinOn ⟨h₀,hh₀,hmem h₀ le_rfl⟩ (continuous_objective v).continuousOn
  refine ⟨h,hh.1,fun k hk => ?_⟩
  by_cases hkb : objective v k≤B
  · exact hmin ⟨hk,hmem k hkb⟩
  · exact (hmin ⟨hh₀,hmem h₀ le_rfl⟩).trans (le_of_not_ge hkb)

lemma projection_unique (S : System V E) (b v h k : V → ℝ)
    (hh : IsProjection S b v h) (hk : IsProjection S b v k) : h=k := by
  have h := projection_parameter_stability S b b v v h k 0 le_rfl hh hk
    (fun x _ => by simp) (fun x _ => by simp)
  funext x
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (h x))

noncomputable def project (S : System V E) (b : V → ℝ) (hne : (feasible S b).Nonempty) (v : V → ℝ) : V → ℝ :=
  Classical.choose (exists_projection S b v hne)

lemma project_spec (S : System V E) (b : V → ℝ) (hne : (feasible S b).Nonempty) (v : V → ℝ) :
    IsProjection S b v (project S b hne v) := Classical.choose_spec (exists_projection S b v hne)

lemma project_eq_self (S : System V E) (b : V → ℝ) (hne : (feasible S b).Nonempty)
    (v : V → ℝ) (hv : v∈feasible S b) : project S b hne v=v := by
  apply projection_unique S b v _ v (project_spec S b hne v)
  refine ⟨hv,?_⟩
  intro k hk
  simpa [objective] using objective_nonneg v k

noncomputable def recursion (S : System V E) (b : V → ℝ) (hne : (feasible S b).Nonempty)
    (h₀ : V → ℝ) (increments : ℕ → V → ℝ) : ℕ → V → ℝ
  | 0 => h₀
  | n+1 => project S b hne (fun x => recursion S b hne h₀ increments n x+increments n x)

theorem recursion_parameter_stability (S : System V E) (b₁ b₂ : V → ℝ)
    (hne₁ : (feasible S b₁).Nonempty) (hne₂ : (feasible S b₂).Nonempty)
    (h₁ h₂ : V → ℝ) (increments : ℕ → V → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hb : ∀ x∈S.pins,|b₁ x-b₂ x|≤δ) (hh : ∀ x,|h₁ x-h₂ x|≤δ) :
    ∀ n x,|recursion S b₁ hne₁ h₁ increments n x-recursion S b₂ hne₂ h₂ increments n x|≤δ := by
  intro n
  induction n with
  | zero => exact hh
  | succ n hn =>
    exact projection_parameter_stability S b₁ b₂ _ _ _ _ δ hδ (project_spec S b₁ hne₁ _) (project_spec S b₂ hne₂ _) hb
      (fun x _ => by simpa only [add_sub_add_right_eq_sub] using hn x)

omit [Fintype V] in
theorem limit_parameter_stability {ι : Type*} {l : Filter ι} [l.NeBot]
    (H₁ H₂ : ι → V → ℝ) (h₁ h₂ : V → ℝ) (δ : ℝ)
    (hH : ∀ i x,|H₁ i x-H₂ i x|≤δ)
    (hlim₁ : ∀ x,Filter.Tendsto (fun i => H₁ i x) l (nhds (h₁ x)))
    (hlim₂ : ∀ x,Filter.Tendsto (fun i => H₂ i x) l (nhds (h₂ x))) :
    ∀ x,|h₁ x-h₂ x|≤δ := by
  intro x
  exact le_of_tendsto ((hlim₁ x).sub (hlim₂ x)).abs (Filter.Eventually.of_forall fun i => hH i x)

end ProjectionComparison

end OAI
