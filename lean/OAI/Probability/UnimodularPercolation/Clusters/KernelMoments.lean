import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.Resampling

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeletedDomainPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem inducedSusceptibility_nonneg (G : BondGraph V E) (D : Set V)
    (p : unitInterval) (x : V) : 0 ≤ inducedSusceptibility G D p x := by
  unfold inducedSusceptibility
  split_ifs
  · exact restrictedSusceptibility_nonneg G _ p x
  · rfl

noncomputable def deletedBoundaryPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) : ℝ :=
  ∑ a ∈ ((finite_reachBall hloc x M).toFinset.filter (· ∉ D)),
    ∑ b ∈ neighbors G hloc a, inducedSusceptibility G D p b

theorem deletedBoundaryPotential_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) :
    0 ≤ deletedBoundaryPotential G hloc D p x M := by
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => inducedSusceptibility_nonneg G D p b))

theorem le_deletedBoundaryPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) (a b : V)
    (ha : a ∈ reachBall G x M) (haD : a ∉ D) (hab : Adj G a b) :
    inducedSusceptibility G D p b ≤ deletedBoundaryPotential G hloc D p x M := by
  apply le_trans (Finset.single_le_sum (fun z _ => inducedSusceptibility_nonneg G D p z)
    ((mem_neighbors G hloc a b).mpr hab))
  apply Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun y _ => inducedSusceptibility_nonneg G D p y))
  exact Finset.mem_filter.mpr ⟨(finite_reachBall hloc x M).mem_toFinset.mpr ha,haD⟩

noncomputable def deletedLocalPotential (G : BondGraph V E) (D : Set V) (p : unitInterval)
    (ω : Set E) (x : V) (M : ℕ) : ℝ :=
  if x ∈ D then intrinsicPotentialMax G (ω ∩ internalEdges G D) x M (inducedSusceptibility G D p) else 0

theorem deletedLocalPotential_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (ω : Set E) (x : V) (M : ℕ) :
    0 ≤ deletedLocalPotential G D p ω x M := by
  unfold deletedLocalPotential
  split_ifs
  · rw [intrinsicPotentialMax_eq G hloc]
    exact inducedSusceptibility_nonneg G D p _
  · rfl

 

theorem short_path_deleted_potential_bound [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (D : Set V)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (ω : Set E) (x y : V) (M : ℕ)
    (l : List E) (hl : Along G x l y) (hlen : l.length ≤ M) (ho : ∀ e ∈ l, e ∈ ω)
    (hfin : ∀ a, Summable (fun z => (law p).real {η | Conn G (η ∩ internalEdges G D) a z})) :
    inducedSusceptibility G D p y ≤ deletedLocalPotential G D p ω x M +
      (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M := by
  have hpM : 0 ≤ (p:ℝ)^(-(M:ℤ)) := zpow_nonneg p.2.1 _
  have hn := deletedLocalPotential_nonneg G hloc D p ω x M
  have hb := deletedBoundaryPotential_nonneg G hloc D p x M
  by_cases hy : y ∈ D
  · rcases hl.last_entrance D hy with ⟨hx,hall⟩ | ⟨a,b,e,l₁,l₂,heq,h₁,he,ha,hbD,h₂,hs⟩
    · have hreach : y ∈ intrinsicBall G (ω ∩ internalEdges G D) x M :=
        ⟨l,hl,hlen,fun e he => ⟨ho e he,hall e he⟩⟩
      have hh := le_intrinsicPotentialMax G hloc _ x M (inducedSusceptibility G D p) y hreach
      change _ ≤ (if x ∈ D then _ else 0) + _
      rw [ite_eq_left hx]
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hpM hb))
    · have hlen₂ : l₂.length ≤ M := by subst l; simp only [List.length_append,List.length_cons] at hlen; omega
      have hpath := restrictedSusceptibility_short_path_bound G (internalEdges G D) p hp h₂ hs M hlen₂ hfin
      have hχ : inducedSusceptibility G D p y ≤ (p:ℝ)^(-(M:ℤ))*inducedSusceptibility G D p b := by
        simpa only [inducedSusceptibility,ite_eq_left hy,ite_eq_left hbD] using hpath
      have haBall : a ∈ reachBall G x M := reachBall_mono G x
        (show l₁.length ≤ M by subst l; simp only [List.length_append,List.length_cons] at hlen; omega) h₁.mem_reachBall
      exact hχ.trans ((mul_le_mul_of_nonneg_left
        (le_deletedBoundaryPotential G hloc D p x M a b haBall ha ⟨e,he⟩) hpM).trans
          (le_add_of_nonneg_left hn))
  · rw [inducedSusceptibility,ite_eq_right hy]
    exact add_nonneg hn (mul_nonneg hpM hb)

end DeletedDomainPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalKernelAction
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem summable_mass_action (q : LocalEndpointRule G hloc O M L)
    (ω : Set E) (x : V) (f : V → ℝ) : Summable (fun y => q.mass ω x y * f y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  rw [q.outside_ball_zero ω x y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul]

theorem summable_kernel_action (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x : V) (f : V → ℝ) : Summable (fun y => q.kernel p x y * f y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  rw [q.kernel_outside_ball_zero p x y (by simpa only [Set.Finite.mem_toFinset] using hy),zero_mul]

theorem integrable_mass_action (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x : V) (f : V → ℝ) :
    Integrable (fun ω => ∑' y, q.mass ω x y * f y) (law p) := by
  apply integrable_finite_local (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset) p
  intro ω
  exact tsum_congr (fun y => congrArg (· * f y) (q.locality ω x y))

theorem kernel_action_integral (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x : V) (f : V → ℝ) :
    (∑' y, q.kernel p x y * f y) = ∫ ω, (∑' y, q.mass ω x y * f y) ∂law p := by
  let B := (finite_reachBall hloc x M).toFinset
  have h₁ : (∑' y, q.kernel p x y*f y) = ∑ y ∈ B, q.kernel p x y*f y :=
    tsum_eq_sum fun y hy => by
      rw [q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul]
  have h₂ (ω : Set E) : (∑' y, q.mass ω x y*f y) = ∑ y ∈ B, q.mass ω x y*f y :=
    tsum_eq_sum fun y hy => by
      rw [q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy),zero_mul]
  rw [h₁]
  simp_rw [h₂]
  rw [integral_finsetSum B (fun y _ => (q.integrable_mass p x y).mul_const (f y))]
  apply Finset.sum_congr rfl
  intro y _
  exact (integral_mul_const (f y) (fun ω => q.mass ω x y)).symm

theorem mass_action_le (q : LocalEndpointRule G hloc O M L)
    (ω : Set E) (x : V) (f : V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ y, q.mass ω x y ≠ 0 → f y ≤ C) :
    (∑' y, q.mass ω x y * f y) ≤ C := by
  calc
    _ ≤ ∑' y, q.mass ω x y * C := by
      apply (q.summable_mass_action ω x f).tsum_le_tsum _ ((q.summable_mass ω x).mul_right C)
      intro y
      by_cases h : q.mass ω x y = 0
      · simp only [h,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hf y h) (q.nonneg ω x y)
    _ = (∑' y, q.mass ω x y)*C := tsum_mul_right
    _ ≤ C := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (q.row_le_one ω x) hC

end LocalEndpointRule
end LocalKernelAction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalMapDeletedPotential
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_deletedLocalPotential (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : Set V) (p : unitInterval) (x : V) (M : ℕ) :
    Integrable (fun ω => deletedLocalPotential G D p ω x M) (law p) := by
  by_cases hx : x ∈ D
  · simp only [deletedLocalPotential,ite_eq_left hx]
    exact integrable_finite_local _ p _ (fun ω =>
      intrinsicPotentialMax_domain_local G hloc (internalEdges G D) ω x M (inducedSusceptibility G D p))
  · simp only [deletedLocalPotential,ite_eq_right hx]
    exact integrable_const 0

theorem integral_deletedLocalPotential_le
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (D : Set V) (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) (x : V) (M : ℕ) :
    (∫ ω, deletedLocalPotential G D p ω x M ∂law p) ≤
      (1+(1-(p:ℝ))/p*M)*inducedSusceptibility G D p x := by
  by_cases hx : x ∈ D
  · simp only [deletedLocalPotential,ite_eq_left hx]
    exact maximal_induced_susceptibility_bound G hloc hqt D x hx M p hp hpc
  · simp only [deletedLocalPotential,inducedSusceptibility,ite_eq_right hx,integral_zero,mul_zero,le_refl]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem kernel_deleted_potential_bound
    [Countable V] [Countable E] [Nonempty V]
    (q : LocalEndpointRule G hloc O M L) (hqt : QuasiTransitive G)
    (D : Set V) (p : unitInterval) (hp : 0 < (p:ℝ)) (hpc : p < pc G) (x : V) :
    (∑' y, q.kernel p x y * inducedSusceptibility G D p y) ≤
      (1+(1-(p:ℝ))/p*M)*inducedSusceptibility G D p x +
        (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M := by
  let f := inducedSusceptibility G D p
  let C := (p:ℝ)^(-(M:ℤ))*deletedBoundaryPotential G hloc D p x M
  have hC : 0 ≤ C := mul_nonneg (zpow_nonneg p.2.1 _) (deletedBoundaryPotential_nonneg G hloc D p x M)
  have hpoint (ω : Set E) : (∑' y, q.mass ω x y * f y) ≤ deletedLocalPotential G D p ω x M + C := by
    apply q.mass_action_le ω x f _ (add_nonneg (deletedLocalPotential_nonneg G hloc D p ω x M) hC)
    intro y hy
    obtain ⟨_,_,hxy,hfin,hcap,_⟩ := q.support ω x y hy
    obtain ⟨l,hl,hlen,ho⟩ := conn_short_of_cluster_cap G ω x y hxy hfin M hcap
    exact short_path_deleted_potential_bound G hloc D p hp ω x y M l hl hlen ho
      (summable_restrictedTwoPoint G hloc hqt p hpc (internalEdges G D))
  rw [q.kernel_action_integral]
  have hi := integrable_deletedLocalPotential G hloc D p x M
  calc
    _ ≤ ∫ ω, deletedLocalPotential G D p ω x M + C ∂law p :=
      integral_mono (q.integrable_mass_action p x f) (hi.add (integrable_const C)) hpoint
    _ = (∫ ω, deletedLocalPotential G D p ω x M ∂law p) + C := by
      rw [integral_add hi (integrable_const C)]; simp
    _ ≤ _ := by
      have hh := integral_deletedLocalPotential_le G hloc hqt D p hp hpc x M
      dsimp [C]
      linarith

end LocalEndpointRule
end LocalMapDeletedPotential
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OrbitKernelTransport
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem orbit_kernel_column_eq_row
    (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (K : V → V → ℝ)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (hout : ∀ x y, x ∉ vertexOrbit G (root i₀) → K x y = 0)
    (hin : ∀ x y, y ∉ vertexOrbit G (root i₀) → K x y = 0)
    (hr : ∀ x, Summable (K x)) (hc : ∀ y, Summable (fun x => K x y))
    (y : V) (hy : y ∈ vertexOrbit G (root i₀)) :
    (∑' x, K x y) = ∑' z, K (root i₀) z := by
  let O := vertexOrbit G (root i₀)
  let w : ι → ℝ := fun i => if root i ∈ O then weight i else 0
  have hrow (x : V) (hx : x ∈ O) : (∑' z, K x z) = ∑' z, K (root i₀) z := by
    obtain ⟨a,b,ha,rfl⟩ := hx
    rw [← a.tsum_eq (fun z => K (a (root i₀)) z)]
    exact tsum_congr (hcov a b ha (root i₀))
  have hcol (x : V) (hx : x ∈ O) : (∑' z, K z x) = ∑' z, K z (root i₀) := by
    obtain ⟨a,b,ha,rfl⟩ := hx
    rw [← a.tsum_eq (fun z => K z (a (root i₀)))]
    exact tsum_congr (fun z => hcov a b ha z (root i₀))
  have ho : root i₀ ∈ O := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e; simp
  have hw' (i : ι) : 0 ≤ w i := by
    dsimp [w]; split_ifs
    · exact hw i
    · rfl
  have hpos : 0 < ∑ i, w i := by
    have hi := Finset.single_le_sum (fun i _ => hw' i) (Finset.mem_univ i₀)
    have he : w i₀ = weight i₀ := ite_eq_left ho
    rw [he] at hi
    exact hw₀.trans_le hi
  have ht := htr.real root weight Γ K
    (by intro a ha x z; obtain ⟨b,hb⟩ := hΓ a ha; exact hcov a b hb x z) hr hc
  have h₁ (i : ι) : weight i * (∑' z, K (root i) z) = w i * (∑' z, K (root i₀) z) := by
    by_cases hi : root i ∈ O
    · rw [hrow (root i) hi]; simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, K (root i) z) = 0 := by simp only [hout _ _ hi,tsum_zero]
      rw [he,mul_zero]
  have h₂ (i : ι) : weight i * (∑' z, K z (root i)) = w i * (∑' z, K z (root i₀)) := by
    by_cases hi : root i ∈ O
    · rw [hcol (root i) hi]; simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, K z (root i)) = 0 := by simp only [hin _ _ hi,tsum_zero]
      rw [he,mul_zero]
  simp_rw [h₁,h₂] at ht
  rw [← Finset.sum_mul,← Finset.sum_mul] at ht
  rw [hcol y hy]
  exact (mul_left_cancel₀ (ne_of_gt hpos) ht).symm

 

theorem operator_norm_le_absolute_sums (K : V → V → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hr : ∀ x (S : Finset V), (∑ y ∈ S, |K x y|) ≤ D)
    (hc : ∀ y (S : Finset V), (∑ x ∈ S, |K x y|) ≤ D)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) : ‖A‖ ≤ D := by
  obtain ⟨B,hBn,hB⟩ := exists_operator_of_row_column_bound (fun x y => |K x y|) D hD
    (fun _ _ => abs_nonneg _) hr hc
  obtain ⟨A',hAn,hA'⟩ := exists_operator_of_matrix_domination
    (fun x y => |K x y|) K (fun _ _ => abs_nonneg _) (fun _ _ => le_rfl) B hB
  have he := kernel_extension_unique hA hA'
  rw [he]
  exact hAn.trans hBn

end OrbitKernelTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointDifference
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)

noncomputable def kernelDifference (p r : unitInterval) (x y : V) : ℝ :=
  |q.normalizedKernel o p x y - q.normalizedKernel o r x y|
noncomputable def differenceRow (p r : unitInterval) : ℝ := ∑' y, q.kernelDifference o p r o y

theorem kernelDifference_nonneg (p r : unitInterval) (x y : V) :
    0 ≤ q.kernelDifference o p r x y := abs_nonneg _

theorem kernelDifference_covariant (p r : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x y : V) :
    q.kernelDifference o p r (a x) (a y) = q.kernelDifference o p r x y := by
  simp only [kernelDifference,normalizedKernel,q.kernel_covariant p a b ha,q.kernel_covariant r a b ha]

theorem kernelDifference_outside (p r : unitInterval) (x y : V) (hy : y ∉ reachBall G x M) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_outside_ball_zero p x y hy,
    q.kernel_outside_ball_zero r x y hy,mul_zero,sub_self,abs_zero]

theorem kernelDifference_reverse_outside (p r : unitInterval) (x y : V) (hx : x ∉ reachBall G y M) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_outside_reverse_ball_zero p x y hx,
    q.kernel_outside_reverse_ball_zero r x y hx,mul_zero,sub_self,abs_zero]

theorem kernelDifference_start (p r : unitInterval) (x y : V) (hx : x ∉ vertexOrbit G o) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_zero_of_start_not_mem p x y hx,
    q.kernel_zero_of_start_not_mem r x y hx,mul_zero,sub_self,abs_zero]

theorem kernelDifference_end (p r : unitInterval) (x y : V) (hy : y ∉ vertexOrbit G o) :
    q.kernelDifference o p r x y = 0 := by
  simp only [kernelDifference,normalizedKernel,q.kernel_zero_of_end_not_mem p x y hy,
    q.kernel_zero_of_end_not_mem r x y hy,mul_zero,sub_self,abs_zero]

theorem summable_kernelDifference (p r : unitInterval) (x : V) :
    Summable (q.kernelDifference o p r x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  exact q.kernelDifference_outside o p r x y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem summable_kernelDifference_column (p r : unitInterval) (y : V) :
    Summable (fun x => q.kernelDifference o p r x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y M).toFinset)
  intro x hx
  exact q.kernelDifference_reverse_outside o p r x y (by simpa only [Set.Finite.mem_toFinset] using hx)

theorem differenceRow_nonneg (p r : unitInterval) : 0 ≤ q.differenceRow o p r :=
  tsum_nonneg (q.kernelDifference_nonneg o p r o)

theorem differenceRow_finite (p r : unitInterval) :
    q.differenceRow o p r = ∑ y ∈ (finite_reachBall hloc o M).toFinset, q.kernelDifference o p r o y := by
  apply tsum_eq_sum
  intro y hy
  exact q.kernelDifference_outside o p r o y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem kernelDifference_row_le (p r : unitInterval) (x : V) :
    (∑' y, q.kernelDifference o p r x y) ≤ q.differenceRow o p r := by
  by_cases hx : x ∈ vertexOrbit G o
  · obtain ⟨a,b,ha,rfl⟩ := hx
    rw [← a.tsum_eq (fun y => q.kernelDifference o p r (a o) y)]
    exact le_of_eq (tsum_congr (q.kernelDifference_covariant o p r a b ha o))
  · simpa only [q.kernelDifference_start o p r x _ hx,tsum_zero] using q.differenceRow_nonneg o p r

 

theorem norm_sub_le_differenceRow {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (ho : o = root i₀)
    (p r : unitInterval) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel o p x y : ℂ))
    (hB : ∀ x y, B (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel o r x y : ℂ)) :
    ‖A-B‖ ≤ q.differenceRow o p r := by
  subst o
  have hc (y : V) : (∑' x, q.kernelDifference (root i₀) p r x y) ≤ q.differenceRow (root i₀) p r := by
    by_cases hy : y ∈ vertexOrbit G (root i₀)
    · exact (orbit_kernel_column_eq_row G root weight Γ htr hΓ hw i₀ hw₀
        (q.kernelDifference (root i₀) p r) (q.kernelDifference_covariant (root i₀) p r)
        (q.kernelDifference_start (root i₀) p r) (q.kernelDifference_end (root i₀) p r)
        (q.summable_kernelDifference (root i₀) p r) (q.summable_kernelDifference_column (root i₀) p r) y hy).le
    · simpa only [q.kernelDifference_end (root i₀) p r _ y hy,tsum_zero] using
        q.differenceRow_nonneg (root i₀) p r
  apply operator_norm_le_absolute_sums
    (fun x y => q.normalizedKernel (root i₀) p x y-q.normalizedKernel (root i₀) r x y)
    _ (q.differenceRow_nonneg (root i₀) p r)
  · intro x S
    exact ((q.summable_kernelDifference (root i₀) p r x).sum_le_tsum S
      (fun y _ => q.kernelDifference_nonneg (root i₀) p r x y)).trans (q.kernelDifference_row_le (root i₀) p r x)
  · intro y S
    exact ((q.summable_kernelDifference_column (root i₀) p r y).sum_le_tsum S
      (fun x _ => q.kernelDifference_nonneg (root i₀) p r x y)).trans (hc y)
  · intro x y
    change A (lp.single 2 y (1:ℂ)) x - B (lp.single 2 y (1:ℂ)) x = _
    rw [hA,hB,Complex.ofReal_sub]

end LocalEndpointRule
end EndpointDifference
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section EndpointOperatorContinuity
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem exists_normalized_operator_all {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (p : unitInterval) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, ‖A‖ ≤ 1 ∧
      ∀ x y, A (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  by_cases hu : q.successProbability p (root i₀) = 0
  · refine ⟨0,by simp,?_⟩
    intro x y
    simp only [normalizedKernel,hu,inv_zero,zero_mul,Complex.ofReal_zero,
      zero_apply,lp.coeFn_zero,Pi.zero_apply]
  · obtain ⟨A,_,hA,hK⟩ := q.exists_normalized_operator root weight Γ htr hΓ hw i₀ hw₀ p
      (lt_of_le_of_ne (q.successProbability_nonneg p (root i₀)) (Ne.symm hu))
    exact ⟨A,hA,hK⟩

theorem continuousAt_differenceRow (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p₀ : unitInterval)
    (hu : q.successProbability p₀ o ≠ 0) :
    ContinuousAt (fun p => q.differenceRow o p p₀) p₀ := by
  simp_rw [q.differenceRow_finite o]
  apply tendsto_finsetSum
  intro y _
  exact ((((q.continuous_successProbability o).continuousAt.inv₀ hu).mul
    (q.continuous_kernel o y).continuousAt).sub continuousAt_const).abs

 

theorem exists_continuous_normalized_operators {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) :
    ∃ A : unitInterval → (Hilbert V →L[ℂ] Hilbert V),
      (∀ p, ‖A p‖ ≤ 1) ∧
      (∀ p x y, A p (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel (root i₀) p x y : ℂ)) ∧
      ∀ p, q.successProbability p (root i₀) ≠ 0 → ContinuousAt A p := by
  choose A hn hK using q.exists_normalized_operator_all root weight Γ htr hΓ hw i₀ hw₀
  refine ⟨A,hn,hK,?_⟩
  intro p hu
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun r => norm_nonneg (A r-A p))
    (fun r => q.norm_sub_le_differenceRow (root i₀) root weight Γ htr hΓ hw i₀ hw₀ rfl r p (A r) (A p) (hK r) (hK p))
  have h := (q.continuousAt_differenceRow (root i₀) p hu).tendsto
  have hz : q.differenceRow (root i₀) p p = 0 := by
    simp only [differenceRow,kernelDifference,sub_self,abs_zero,tsum_zero]
  rwa [hz] at h

end LocalEndpointRule
end EndpointOperatorContinuity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ThreeArmGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem Along.first_entrance {G : BondGraph V E} {x y : V} {l : List E}
    (hl : Along G x l y) (D : Set V) (hy : y ∈ D) :
    ∃ z ∈ D, ∃ k : List E, Along G x k z ∧ k ⊆ l ∧ ∀ e ∈ k, e ∉ internalEdges G D := by
  induction hl with
  | nil => exact ⟨_,hy,[],.nil _,by simp,by simp⟩
  | @cons x z y l e he ht ih =>
    by_cases hx : x ∈ D
    · exact ⟨x,hx,[],.nil _,by simp,by simp⟩
    · obtain ⟨w,hw,k,hk,hsub,hout⟩ := ih hy
      refine ⟨w,hw,e::k,.cons e he hk,?_,?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub hd)
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · intro h
          exact hx ((mem_internalEdges_of_ends G D d x z he).mp h).1
        · exact hout d hd

 

theorem conn_three_disjoint_arms (G : BondGraph V E) (ω : Set E) (x y z : V)
    (hxy : Conn G ω x y) (hxz : Conn G ω x z) :
    ∃ w, ω ∈ DisjointOccurrence {η | Conn G η x w}
      (DisjointOccurrence {η | Conn G η w y} {η | Conn G η w z}) := by
  obtain ⟨p⟩ := (conn_iff_reachable G ω x y).mp hxy
  let t := p.toPath
  let D : Set V := {a | a ∈ t.val.support}
  obtain ⟨l,hl,_,ho⟩ := conn_exists_bond_trail G (conn_symm G ω hxz)
  obtain ⟨w,hw,k,hk,hsub,hout⟩ := hl.first_entrance D t.val.start_mem_support
  obtain ⟨l₁,h₁,he₁,ho₁⟩ := walk_lift_bonds G ω (t.val.takeUntil w hw)
  obtain ⟨l₂,h₂,he₂,ho₂⟩ := walk_lift_bonds G ω (t.val.dropUntil w hw)
  have h₁in (e : E) (he : e ∈ l₁) : e ∈ internalEdges G D := by
    have hh : G e ∈ (t.val.takeUntil w hw).edges := he₁ ▸ List.mem_map_of_mem he
    have hh' := t.val.edges_takeUntil_subset_edges hw hh
    intro a ha
    exact SimpleGraph.Walk.mem_support_of_mem_edges hh' ha
  have h₂in (e : E) (he : e ∈ l₂) : e ∈ internalEdges G D := by
    have hh : G e ∈ (t.val.dropUntil w hw).edges := he₂ ▸ List.mem_map_of_mem he
    have hh' := t.val.edges_dropUntil_subset_edges hw hh
    intro a ha
    exact SimpleGraph.Walk.mem_support_of_mem_edges hh' ha
  have h12 : Disjoint l₁.toFinset l₂.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e he₁' he₂'
    have hp := t.property.isTrail.disjoint_edges_takeUntil_dropUntil hw
    exact List.disjoint_left.mp hp (he₁ ▸ List.mem_map_of_mem (List.mem_toFinset.mp he₁'))
      (he₂ ▸ List.mem_map_of_mem (List.mem_toFinset.mp he₂'))
  have h13 : Disjoint l₁.toFinset k.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e he hk'
    exact hout e (List.mem_toFinset.mp hk') (h₁in e (List.mem_toFinset.mp he))
  have h23 : Disjoint l₂.toFinset k.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e he hk'
    exact hout e (List.mem_toFinset.mp hk') (h₂in e (List.mem_toFinset.mp he))
  have hkopen (e : E) (he : e ∈ k) : e ∈ ω := ho e (hsub he)
  refine ⟨w,l₁.toFinset,l₂.toFinset ∪ k.toFinset,?_,?_,Finset.disjoint_union_right.mpr ⟨h12,h13⟩,?_,?_⟩
  · intro e he; exact ho₁ e (List.mem_toFinset.mp he)
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact ho₂ e (List.mem_toFinset.mp he)
    · exact hkopen e (List.mem_toFinset.mp he)
  · exact h₁.conn (fun e he => List.mem_toFinset.mpr he)
  · refine ⟨l₂.toFinset,k.toFinset,?_,?_,h23,?_,?_⟩
    · exact_mod_cast Finset.subset_union_left
    · exact_mod_cast Finset.subset_union_right
    · exact h₂.conn (fun e he => List.mem_toFinset.mpr he)
    · exact conn_symm G _ (hk.conn (fun e he => List.mem_toFinset.mpr he))

end ThreeArmGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ThreeArmProbability
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem bk_ennreal [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    law p (DisjointOccurrence A B) ≤ law p A * law p B := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact bk p A B hA hB hfA hfB

 

theorem three_arm_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y z : V) :
    law p {ω | Conn G ω x y ∧ Conn G ω x z} ≤
      ∑' w, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} := by
  let C := fun a b : V => {ω : Set E | Conn G ω a b}
  have hup (a b : V) : IsUpperSet (C a b) := fun _ _ h hconn => conn_mono G h hconn
  have hf (a b : V) : FiniteWitness (C a b) := finiteWitness_conn G a b
  have hb (w : V) : law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) ≤
      law p (C x w) * law p (C w y) * law p (C w z) := by
    calc
      _ ≤ law p (C x w) * law p (DisjointOccurrence (C w y) (C w z)) :=
        bk_ennreal p _ _ (hup x w) (disjointOccurrence_upper _ _) (hf x w) (finiteWitness_disjointOccurrence _ _)
      _ ≤ law p (C x w) * (law p (C w y)*law p (C w z)) :=
        mul_le_mul_right (bk_ennreal p _ _ (hup w y) (hup w z) (hf w y) (hf w z)) _
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ ≤ law p (⋃ w, DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) := by
      apply measure_mono
      intro ω h
      obtain ⟨w,hw⟩ := conn_three_disjoint_arms G ω x y z h.1 h.2
      exact Set.mem_iUnion.mpr ⟨w,hw⟩
    _ ≤ ∑' w, law p (DisjointOccurrence (C x w) (DisjointOccurrence (C w y) (C w z))) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hb

 

theorem three_arm_double_sum_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, (∑' y, law p {ω | Conn G ω x y}) ≤ C) (x : V) :
    (∑' y, ∑' z, law p {ω | Conn G ω x y ∧ Conn G ω x z}) ≤ C^3 := by
  calc
    _ ≤ ∑' y, ∑' z, ∑' w, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} :=
      ENNReal.tsum_le_tsum (fun y => ENNReal.tsum_le_tsum (fun z => three_arm_bound G p x y z))
    _ = ∑' w, law p {ω | Conn G ω x w} * (∑' y, law p {ω | Conn G ω w y}) *
        (∑' z, law p {ω | Conn G ω w z}) := by
      calc
        _ = ∑' y, ∑' w, ∑' z, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} := by
          apply tsum_congr
          intro y
          exact ENNReal.tsum_comm
        _ = ∑' w, ∑' y, ∑' z, law p {ω | Conn G ω x w} * law p {ω | Conn G ω w y} * law p {ω | Conn G ω w z} := ENNReal.tsum_comm
        _ = _ := by simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ ∑' w, law p {ω | Conn G ω x w} * C * C :=
      ENNReal.tsum_le_tsum (fun w => mul_le_mul' (mul_le_mul_right (hC w) _) (hC w))
    _ = (∑' w, law p {ω | Conn G ω x w}) * C * C := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right]
    _ ≤ C*C*C := mul_le_mul_left (mul_le_mul_left (hC x) C) C
    _ = C^3 := by ring

end ThreeArmProbability
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterMassMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def clusterMass (G : BondGraph V E) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if Conn G ω x y then 1 else 0

theorem measurable_clusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : Measurable (fun ω => clusterMass G ω x) := by
  apply Measurable.tsum
  intro y
  exact Measurable.ite (measurableSet_conn G x y) measurable_const measurable_const

theorem clusterMass_eq_ncard (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : clusterMass G ω x = (cluster G ω x).ncard := by
  change (∑' y, if y ∈ cluster G ω x then (1:ℝ≥0∞) else 0) = _
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    simp only [Set.Finite.mem_toFinset] at hy
    simp only [ite_eq_right hy])]
  have he : (∑ y ∈ hf.toFinset, if y ∈ cluster G ω x then (1:ℝ≥0∞) else 0) = ∑ _y ∈ hf.toFinset, (1:ℝ≥0∞) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left (hf.mem_toFinset.mp hy)
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

theorem lintegral_clusterMass [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) :
    (∫⁻ ω, clusterMass G ω x ∂law p) = ∑' y, law p {ω | Conn G ω x y} := by
  unfold clusterMass
  rw [lintegral_tsum (fun y => (Measurable.ite (measurableSet_conn G x y) measurable_const measurable_const).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) (measurableSet_conn G x y))

theorem clusterMass_sq (G : BondGraph V E) (ω : Set E) (x : V) :
    clusterMass G ω x ^ 2 = ∑' y, ∑' z, if Conn G ω x y ∧ Conn G ω x z then (1:ℝ≥0∞) else 0 := by
  rw [pow_two,clusterMass]
  rw [←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro y
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  split_ifs <;> simp_all

theorem lintegral_clusterMass_sq [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x : V) :
    (∫⁻ ω, clusterMass G ω x ^ 2 ∂law p) =
      ∑' y, ∑' z, law p {ω | Conn G ω x y ∧ Conn G ω x z} := by
  have hm (y z : V) : Measurable (fun ω : Set E => if Conn G ω x y ∧ Conn G ω x z then (1:ℝ≥0∞) else 0) :=
    Measurable.ite ((measurableSet_conn G x y).inter (measurableSet_conn G x z)) measurable_const measurable_const
  simp_rw [clusterMass_sq]
  rw [lintegral_tsum (fun y => (Measurable.tsum (fun z => hm y z)).aemeasurable)]
  apply tsum_congr
  intro y
  rw [lintegral_tsum (fun z => (hm y z).aemeasurable)]
  apply tsum_congr
  intro z
  have hs : MeasurableSet {ω : Set E | Conn G ω x y ∧ Conn G ω x z} :=
    (measurableSet_conn G x y).inter (measurableSet_conn G x z)
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) hs)

 
theorem cluster_second_moment_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, (∑' y, law p {ω | Conn G ω x y}) ≤ C) (x : V) :
    (∫⁻ ω, clusterMass G ω x ^ 2 ∂law p) ≤ C^3 := by
  rw [lintegral_clusterMass_sq]
  exact three_arm_double_sum_bound G p C hC x

end ClusterMassMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SubcriticalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem subcritical_cluster_finite_ae (G : BondGraph V E)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hz : (law p).real {ω | (cluster G ω x).Infinite} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! h
    exact (not_le_of_gt hp) (pc_le_of_infinite_cluster_probability_pos G x p h)
  apply ae_iff.mpr
  change law p {ω | (cluster G ω x).Infinite} = 0
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

theorem subcritical_ennreal_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (∑' y, law p {ω | Conn G ω x y}) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  refine ⟨C,hC,fun x => ?_⟩
  have hs := summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)
  have he : (∑' y, law p {ω | Conn G ω x y}) = ENNReal.ofReal (∑' y, twoPoint G p x y) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G p x) hs]
    apply tsum_congr
    intro y
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hs.tsum_le_of_sum_le (hrow x))

 

theorem subcritical_second_moment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p) ∧
      (∫ ω, ((cluster G ω x).ncard:ℝ)^2 ∂law p) ≤ C^3 := by
  obtain ⟨C,hC,hrow⟩ := subcritical_ennreal_row_bound G hloc hqt p hp
  refine ⟨C,hC,fun x => ?_⟩
  have hmeas : Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)^2) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ)^2)).comp (measurable_cluster_ncard G hloc x)
  have hn : 0 ≤ᵐ[law p] (fun ω => ((cluster G ω x).ncard:ℝ)^2) :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have he : (fun ω => ENNReal.ofReal (((cluster G ω x).ncard:ℝ)^2)) =ᵐ[law p]
      (fun ω => clusterMass G ω x ^ 2) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    rw [clusterMass_eq_ncard G ω x hω,ENNReal.ofReal_pow (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  have hbound : (∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)^2) ∂law p) ≤ ENNReal.ofReal (C^3) := by
    rw [lintegral_congr_ae he,ENNReal.ofReal_pow hC]
    exact cluster_second_moment_bound G p _ hrow x
  have hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p) :=
    ⟨hmeas.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hn).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hmeas.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal (pow_nonneg hC _))

end SubcriticalMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def susceptibility (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, twoPoint G p x y

noncomputable def rootSusceptibility (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (p : unitInterval) : ℝ :=
  ∑ i, weight i * susceptibility G p (root i)

theorem susceptibility_nonneg (G : BondGraph V E) (p : unitInterval) (x : V) :
    0 ≤ susceptibility G p x := tsum_nonneg (twoPoint_nonneg G p x)

theorem summable_twoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : Summable (twoPoint G p x) := by
  obtain ⟨_,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  exact summable_of_sum_le (twoPoint_nonneg G p x) (hrow x)

theorem ennreal_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    ENNReal.ofReal (susceptibility G p x) = ∑' y, law p {ω | Conn G ω x y} := by
  rw [susceptibility,ENNReal.ofReal_tsum_of_nonneg (twoPoint_nonneg G p x)
    (summable_twoPoint_subcritical G hloc hqt p hp x)]
  apply tsum_congr
  intro y
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem susceptibility_aut [Countable V] [Countable E] (G : BondGraph V E)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    susceptibility G p (a x) = susceptibility G p x := by
  unfold susceptibility
  rw [←a.tsum_eq]
  simp only [twoPoint_aut G p h]

theorem susceptibility_one_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) : 1 ≤ susceptibility G p x := by
  have hd : twoPoint G p x x = 1 := by
    have he : {ω : Set E | Conn G ω x x} = Set.univ := Set.eq_univ_of_forall (fun _ => conn_refl G _ x)
    simp only [twoPoint,he,measure_univ,ENNReal.toReal_one]
  rw [←hd]
  exact (summable_twoPoint_subcritical G hloc hqt p hp x).le_tsum x (fun _ _ => twoPoint_nonneg G p _ _)

theorem rootSusceptibility_nonneg (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) (p : unitInterval) :
    0 ≤ rootSusceptibility G root weight p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (susceptibility_nonneg G p _))

theorem susceptibility_le_rootSusceptibility [Countable V] [Countable E]
    (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (p : unitInterval) (x : V) :
    susceptibility G p x ≤ c*rootSusceptibility G root weight p := by
  obtain ⟨i,a,b,hab,hax⟩ := hcov x
  rw [←hax,susceptibility_aut G p hab]
  calc
    _ ≤ (c*weight i)*susceptibility G p (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) (susceptibility_nonneg G p _)
    _ = c*(weight i*susceptibility G p (root i)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (susceptibility_nonneg G p _)) (Finset.mem_univ i)) hc

 
theorem susceptibility_eq_integral [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)) (law p) ∧
      susceptibility G p x = ∫ ω, ((cluster G ω x).ncard:ℝ) ∂law p := by
  have hm : Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)
  have hn : 0 ≤ᵐ[law p] (fun ω => ((cluster G ω x).ncard:ℝ)) := Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  have he : (fun ω => ENNReal.ofReal ((cluster G ω x).ncard:ℝ)) =ᵐ[law p] (fun ω => clusterMass G ω x) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    rw [clusterMass_eq_ncard G ω x hω,ENNReal.ofReal_natCast]
  have heq : (∫⁻ ω, ENNReal.ofReal ((cluster G ω x).ncard:ℝ) ∂law p) = ENNReal.ofReal (susceptibility G p x) := by
    rw [lintegral_congr_ae he,lintegral_clusterMass,ennreal_susceptibility G hloc hqt p hp]
  refine ⟨⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hn).mpr (by rw [heq]; exact ENNReal.ofReal_lt_top)⟩,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable,heq,ENNReal.toReal_ofReal (susceptibility_nonneg G p x)]

end SusceptibilityTypes
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteKernelNorm
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem kernel_sum_le_norm_card (K : V → V → ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) (F : Finset V) :
    ∑ x ∈ F, ∑ y ∈ F, K x y ≤ ‖A‖*F.card := by
  have he : inner ℂ (deltaSum F) (A (deltaSum F)) =
      ((∑ x ∈ F, ∑ y ∈ F, K x y : ℝ) : ℂ) := by
    rw [inner_deltaSum]
    simp only [deltaSum,map_sum,lp.coeFn_sum,Finset.sum_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hA x y
  have h := (Complex.re_le_norm (inner ℂ (deltaSum F) (A (deltaSum F)))).trans
    ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)))
  rw [he,Complex.ofReal_re] at h
  calc
    _ ≤ ‖deltaSum F‖*(‖A‖*‖deltaSum F‖) := h
    _ = ‖A‖*‖deltaSum F‖^2 := by ring
    _ = _ := by rw [norm_deltaSum_sq]

 
theorem kernel_average_le_norm (K : V → V → ℝ)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ))
    (F : Finset V) (hF : F.Nonempty) :
    (∑ x ∈ F, ∑ y ∈ F, K x y)/(F.card:ℝ) ≤ ‖A‖ := by
  exact (div_le_iff₀ (Nat.cast_pos.mpr hF.card_pos)).mpr (kernel_sum_le_norm_card K A hA F)

end FiniteKernelNorm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinClusterSlice
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binClusterSlice (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x : V) : Finset V :=
  if h : ClusterWindow G x n (2*n) ω then h.1.toFinset.filter (fun y => y ∈ vertexOrbit G o) else ∅

theorem mem_binClusterSlice (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binClusterSlice G o n ω x ↔ ClusterWindow G x n (2*n) ω ∧ Conn G ω x y ∧ y ∈ vertexOrbit G o := by
  unfold binClusterSlice
  split_ifs with h
  · simp only [Finset.mem_filter,Set.Finite.mem_toFinset,h,true_and,cluster,Set.mem_ofPred_eq]
  · simp only [Finset.notMem_empty,h,false_and]

theorem binClusterSlice_eq_of_conn (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E)
    {x y : V} (h : Conn G ω x y) : binClusterSlice G o n ω x = binClusterSlice G o n ω y := by
  have hc := cluster_eq_of_conn G ω h
  have hw : ClusterWindow G x n (2*n) ω ↔ ClusterWindow G y n (2*n) ω := by
    unfold ClusterWindow
    rw [hc]
  ext z
  simp only [mem_binClusterSlice,hw]
  have hz : Conn G ω x z ↔ Conn G ω y z := by change z ∈ cluster G ω x ↔ z ∈ cluster G ω y; rw [hc]
  rw [hz]

theorem binClusterSlice_nonempty (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x : V)
    (hw : ClusterWindow G x n (2*n) ω) (hx : x ∈ vertexOrbit G o) :
    (binClusterSlice G o n ω x).Nonempty :=
  ⟨x,(mem_binClusterSlice G o n ω x x).mpr ⟨hw,conn_refl _ _ _,hx⟩⟩

theorem binOrbitRowMass_eq_slice (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x : V)
    (hx : x ∈ vertexOrbit G o) :
    binOrbitRowMass G n ω x = (binClusterSlice G o n ω x).card := by
  by_cases hw : ClusterWindow G x n (2*n) ω
  · rw [binOrbitRowMass_eq G n ω x hw,vertexOrbit_eq_of_mem G o x hx]
    simp only [binClusterSlice,dite_eq_left hw]
    rw [←Finset.sum_filter]
    simp
  · rw [binOrbitRowMass_zero G n ω x hw]
    simp only [binClusterSlice,dite_eq_right hw,Finset.card_empty,Nat.cast_zero]

theorem binSizeMass_eq_of_conn (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {x y : V} (hc : Conn G ω x y) : binSizeMass G n ω x = binSizeMass G n ω y := by
  have he := cluster_eq_of_conn G ω hc
  have hw : ClusterWindow G x n (2*n) ω ↔ ClusterWindow G y n (2*n) ω := by
    unfold ClusterWindow
    rw [he]
  by_cases hx : ClusterWindow G x n (2*n) ω
  · rw [binSizeMass_eq G n ω x hx,binSizeMass_eq G n ω y (hw.mp hx),he]
  · have hy := fun h => hx (hw.mpr h)
    simp only [binSizeMass,binMass_zero_of_not_window G n ω x _ hx,
      binMass_zero_of_not_window G n ω y _ hy,tsum_zero]

theorem mem_binClusterSlice_iff_mass (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x y : V) :
    y ∈ binClusterSlice G o n ω x ↔
      binConnectionMass G n ω x y = 1 ∧ y ∈ vertexOrbit G o := by
  rw [mem_binClusterSlice]
  have he : binConnectionMass G n ω x y =
      if ClusterWindow G x n (2*n) ω ∧ Conn G ω x y then 1 else 0 := by
    unfold binConnectionMass ClusterWindow
    congr 1
    apply propext; tauto
  rw [he]
  by_cases h : ClusterWindow G x n (2*n) ω ∧ Conn G ω x y
  · rw [ite_eq_left h]
    simp only [h.1,h.2,true_and]
  · rw [ite_eq_right h]
    simp only [zero_ne_one,false_and]
    tauto

theorem binClusterSlice_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (o : V) (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binClusterSlice G o n ω x = binClusterSlice G o n (ω ∩ (Q : Set E)) x := by
  intro Q
  ext y
  rw [mem_binClusterSlice_iff_mass,mem_binClusterSlice_iff_mass,
    binConnectionMass_local G hloc n ω x y]

end BinClusterSlice
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteClassTransport
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteClassTransport (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (x y : V) : ℝ :=
  if y ∈ S x then t x / (S x).card * ∑ z ∈ S x, K x z else 0

theorem finiteClassTransport_nonneg (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (ht : ∀ x, 0 ≤ t x) (hK : ∀ x y, 0 ≤ K x y) (x y : V) :
    0 ≤ finiteClassTransport S t K x y := by
  unfold finiteClassTransport
  split_ifs
  · exact mul_nonneg (div_nonneg (ht x) (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun z _ => hK x z))
  · rfl

theorem finiteClassTransport_row (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (x : V) :
    (∑' y, finiteClassTransport S t K x y) = t x * ∑ z ∈ S x, K x z := by
  rw [tsum_eq_sum (s := S x) (fun y hy => (show finiteClassTransport S t K x y = 0 from ite_eq_right hy))]
  have he : (∑ y ∈ S x, finiteClassTransport S t K x y) =
      (S x).card * (t x / (S x).card * ∑ z ∈ S x, K x z) := by
    simp only [finiteClassTransport]
    rw [Finset.sum_ite_mem]
    simp only [Finset.inter_self,Finset.sum_const,nsmul_eq_mul]
  rw [he]
  by_cases h : (S x).Nonempty
  · have hc : ((S x).card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.card_pos.ne'
    field_simp
  · have hs := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hs,Finset.card_empty,Nat.cast_zero,Finset.sum_empty,mul_zero]

theorem finiteClassTransport_column (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ)
    (hsym : ∀ x y, y ∈ S x ↔ x ∈ S y)
    (heq : ∀ x y, y ∈ S x → S y = S x)
    (ht : ∀ x y, y ∈ S x → t y = t x) (x : V) :
    (∑' y, finiteClassTransport S t K y x) =
      t x / (S x).card * ∑ y ∈ S x, ∑ z ∈ S x, K y z := by
  rw [tsum_eq_sum (s := S x) (fun y hy => (show finiteClassTransport S t K y x = 0 from
    ite_eq_right (fun h => hy ((hsym x y).mpr h))))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [finiteClassTransport,ite_eq_left ((hsym x y).mp hy),heq x y hy,ht x y hy]

 
theorem finiteClassTransport_column_le (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (ht0 : ∀ x, 0 ≤ t x)
    (hsym : ∀ x y, y ∈ S x ↔ x ∈ S y)
    (heq : ∀ x y, y ∈ S x → S y = S x)
    (ht : ∀ x y, y ∈ S x → t y = t x)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) (x : V) :
    (∑' y, finiteClassTransport S t K y x) ≤ ‖A‖*t x := by
  rw [finiteClassTransport_column S t K hsym heq ht]
  by_cases h : (S x).Nonempty
  · have hh := mul_le_mul_of_nonneg_left (kernel_average_le_norm K A hA (S x) h) (ht0 x)
    simpa only [div_mul_eq_mul_div,mul_div_assoc,mul_comm (t x) ‖A‖] using hh
  · have hs := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hs,Finset.card_empty,Nat.cast_zero,div_zero,Finset.sum_empty,mul_zero]
    exact mul_nonneg (norm_nonneg _) (ht0 x)

end FiniteClassTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinDiagonalClass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitClass (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x : V) : Finset V :=
  if x ∈ vertexOrbit G o then binClusterSlice G o n ω x else ∅

theorem mem_binOrbitClass (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binOrbitClass G o n ω x ↔ x ∈ vertexOrbit G o ∧
      ClusterWindow G x n (2*n) ω ∧ Conn G ω x y ∧ y ∈ vertexOrbit G o := by
  unfold binOrbitClass
  split_ifs with h
  · simp only [mem_binClusterSlice,h,true_and]
  · simp only [Finset.notMem_empty,h,false_and]

theorem binOrbitClass_symm (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binOrbitClass G o n ω x ↔ x ∈ binOrbitClass G o n ω y := by
  have h (x y : V) (hy : y ∈ binOrbitClass G o n ω x) : x ∈ binOrbitClass G o n ω y := by
    obtain ⟨hx,hw,hc,hy⟩ := (mem_binOrbitClass G o n ω x y).mp hy
    have hwy : ClusterWindow G y n (2*n) ω := by
      unfold ClusterWindow at hw ⊢
      rw [←cluster_eq_of_conn G ω hc]
      exact hw
    exact (mem_binOrbitClass G o n ω y x).mpr ⟨hy,hwy,conn_symm G ω hc,hx⟩
  exact ⟨h x y,h y x⟩

theorem binOrbitClass_eq (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∈ binOrbitClass G o n ω x) : binOrbitClass G o n ω y = binOrbitClass G o n ω x := by
  obtain ⟨hx,_,hc,hy⟩ := (mem_binOrbitClass G o n ω x y).mp hy
  simp only [binOrbitClass,ite_eq_left hx,ite_eq_left hy]
  exact (binClusterSlice_eq_of_conn G o n ω hc).symm

theorem binOrbitClass_mass_eq (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∈ binOrbitClass G o n ω x) : binSizeMass G n ω y = binSizeMass G n ω x :=
  (binSizeMass_eq_of_conn G n ω ((mem_binOrbitClass G o n ω x y).mp hy).2.2.1).symm

theorem binOrbitClass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (o : V) (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binOrbitClass G o n ω x = binOrbitClass G o n (ω ∩ (Q : Set E)) x := by
  intro Q
  unfold binOrbitClass
  rw [binClusterSlice_local G hloc o n ω x]

theorem binOrbitClass_mem_covariant (G : BondGraph V E) (o : V)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (n : ℕ) (ω : Set E) (x y : V) :
    y ∈ binOrbitClass G o n (b ⁻¹' ω) x ↔ a y ∈ binOrbitClass G o n ω (a x) := by
  unfold binOrbitClass
  simp only [mem_vertexOrbit_aut_iff G o hab]
  split_ifs
  · simp only [mem_binClusterSlice_iff_mass,binConnectionMass_covariant G hab,
      mem_vertexOrbit_aut_iff G o hab]
  · simp only [Finset.notMem_empty]

theorem binOrbitClass_covariant (G : BondGraph V E) (o : V)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (n : ℕ) (ω : Set E) (x : V) :
    (binOrbitClass G o n (b ⁻¹' ω) x).image a = binOrbitClass G o n ω (a x) := by
  ext y
  constructor
  · rintro hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact (binOrbitClass_mem_covariant G o hab n ω x z).mp hz
  · intro hy
    exact Finset.mem_image.mpr ⟨a.symm y,(binOrbitClass_mem_covariant G o hab n ω x (a.symm y)).mpr
      (by simpa only [Equiv.apply_symm_apply] using hy),a.apply_symm_apply y⟩

theorem binOrbitClass_reach (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∈ binOrbitClass G o n ω x) : y ∈ reachBall G x (2*n) := by
  obtain ⟨_,hw,hc,_⟩ := (mem_binOrbitClass G o n ω x y).mp hy
  exact finite_cluster_subset_reachBall G ω x hw.1 (2*n) hw.2.2.le hc

end BinDiagonalClass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binDiagonalMass (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) : ℝ :=
  finiteClassTransport (binOrbitClass G o n ω) (fun x => binSizeMass G n ω x ^ 2) K x y

theorem binDiagonalMass_nonneg (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y) (ω : Set E) (x y : V) :
    0 ≤ binDiagonalMass G o n K ω x y :=
  finiteClassTransport_nonneg _ _ K (fun _ => sq_nonneg _) hK x y

theorem binDiagonalMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (o : V) (n : ℕ) (K : V → V → ℝ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binDiagonalMass G o n K ω x y = binDiagonalMass G o n K (ω ∩ (Q : Set E)) x y := by
  intro Q
  simp only [binDiagonalMass,finiteClassTransport]
  rw [binOrbitClass_local G hloc o n ω x,binSizeMass_local G hloc n ω x]

theorem binDiagonalMass_integrable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ) (x y : V) :
    Integrable (fun ω => binDiagonalMass G o n K ω x y) (law p) :=
  integrable_finite_local _ p _ (fun ω => binDiagonalMass_local G hloc o n K ω x y)

theorem binDiagonalMass_outside (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hy : y ∉ reachBall G x (2*n)) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hy (binOrbitClass_reach G o n ω x y h))

theorem binDiagonalMass_outside_column (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hx : x ∉ reachBall G y (2*n)) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hx (binOrbitClass_reach G o n ω y x ((binOrbitClass_symm G o n ω x y).mp h)))

theorem binDiagonalMass_row_zero (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hx : x ∉ vertexOrbit G o) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hx ((mem_binOrbitClass G o n ω x y).mp h).1)

theorem binDiagonalMass_column_zero (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) (hy : y ∉ vertexOrbit G o) :
    binDiagonalMass G o n K ω x y = 0 :=
  ite_eq_right (fun h => hy ((mem_binOrbitClass G o n ω x y).mp h).2.2.2)

theorem binDiagonalMass_covariant (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hK : ∀ x y, K (a x) (a y) = K x y) (ω : Set E) (x y : V) :
    binDiagonalMass G o n K (b ⁻¹' ω) x y = binDiagonalMass G o n K ω (a x) (a y) := by
  have hs := binOrbitClass_covariant G o hab n ω x
  have hc : (binOrbitClass G o n (b ⁻¹' ω) x).card = (binOrbitClass G o n ω (a x)).card := by
    rw [←hs,Finset.card_image_of_injective _ a.injective]
  have hsum : (∑ z ∈ binOrbitClass G o n (b ⁻¹' ω) x, K x z) =
      ∑ z ∈ binOrbitClass G o n ω (a x), K (a x) z := by
    rw [←hs,Finset.sum_image (fun _ _ _ _ h => a.injective h)]
    simp only [hK]
  simp only [binDiagonalMass,finiteClassTransport,binOrbitClass_mem_covariant G o hab,
    binSizeMass_covariant G n ω hab,hc,hsum]

theorem binDiagonalMass_row (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x : V) :
    (∑' y, binDiagonalMass G o n K ω x y) =
      binSizeMass G n ω x ^ 2 * ∑ z ∈ binOrbitClass G o n ω x, K x z :=
  finiteClassTransport_row _ _ K x

theorem binDiagonalMass_column (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x : V) :
    (∑' y, binDiagonalMass G o n K ω y x) =
      binSizeMass G n ω x ^ 2 / (binOrbitClass G o n ω x).card *
        ∑ y ∈ binOrbitClass G o n ω x, ∑ z ∈ binOrbitClass G o n ω x, K y z := by
  apply finiteClassTransport_column _ _ K (binOrbitClass_symm G o n ω) (binOrbitClass_eq G o n ω)
  intro x y hy
  rw [binOrbitClass_mass_eq G o n ω x y hy]

theorem binDiagonalMass_column_le (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) (ω : Set E) (x : V) :
    (∑' y, binDiagonalMass G o n K ω y x) ≤ ‖A‖ * binSizeMass G n ω x ^ 2 := by
  apply finiteClassTransport_column_le _ _ K (fun _ => sq_nonneg _)
    (binOrbitClass_symm G o n ω) (binOrbitClass_eq G o n ω) _ A hA
  intro x y hy
  rw [binOrbitClass_mass_eq G o n ω x y hy]

end BinDiagonalTransport
end Percolation

end OAI
