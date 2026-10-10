import OAI.InformationTheory.QuantumCircuit.Transition

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

/-- The real scalar spelling makes the coefficient budget transparent. -/
def reflect {N : ℕ} (D : Count N) : Operator N := 1 - (2:ℝ) • D.zero

def reflectList {N : ℕ} (l : List (Count N)) : Operator N := (l.map reflect).prod

lemma reflectionMatrix_eq {N : ℕ} (R : ReflectionLayer N) : reflectionMatrix R = reflectList R.gates := by
  unfold reflectionMatrix reflectList
  congr 1

lemma reflect_unitary {N : ℕ} (D : Count N) : reflect D ∈ unitary (Operator N) := by
  simpa only [reflect,two_smul] using reflection_unitary D

lemma reflect_disjoint_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute (reflect A) (reflect B) := by
  exact (Commute.one_left _).sub_left
    (((Commute.one_right _).sub_right ((A.disjoint_commute B h).smul_right (2:ℝ))).smul_left (2:ℝ))

lemma reflect_disjoint_zero_commute {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) :
    Commute (reflect A) B.zero :=
  (Commute.one_left _).sub_left ((A.disjoint_commute B h).smul_left (2:ℝ))

def ReflectionLayer.active {N : ℕ} (R : ReflectionLayer N) (A : Count N) : ReflectionLayer N where
  gates := R.gates.filter (fun D => decide (¬Disjoint D.support A.support))
  disjoint := R.disjoint.filter _

lemma ReflectionLayer.active_length {N : ℕ} (R : ReflectionLayer N) (A : Count N) :
    (R.active A).gates.length ≤ A.support.card := by
  apply list_disjoint_hits_length Count.support _ (R.active A).disjoint
  intro D hD
  have h := (List.mem_filter.mp hD).2
  simp only [decide_eq_true_eq] at h
  exact Finset.not_disjoint_iff_nonempty_inter.mp h

lemma ReflectionLayer.active_conjugate {N : ℕ} (R : ReflectionLayer N) (A : Count N) :
    conjugate (reflectionMatrix R) A.zero = conjugate (reflectionMatrix (R.active A)) A.zero := by
  rw [reflectionMatrix_eq,reflectionMatrix_eq]
  apply list_conjugate_filter
  · exact R.disjoint.imp (fun h => reflect_disjoint_commute _ _ h)
  · intro D _; exact reflect_unitary D
  · intro D _ hD
    apply reflect_disjoint_zero_commute
    simpa using hD


/-- Expansion of a disjoint reflection product.  The real coefficients carry
all multiplicities; no commutation of the middle projection is required. -/
def reflectionTerms {N : ℕ} : List (Count N) → List (ℝ × Count N)
  | [] => [(1,Count.empty)]
  | A::l => reflectionTerms l ++ (reflectionTerms l).map (fun p => (-2*p.1,A.join p.2))

lemma reflectionTerms_support {N : ℕ} (l : List (Count N)) :
    ∀ p ∈ reflectionTerms l, ∀ i ∈ p.2.support, ∃ A ∈ l, i ∈ A.support := by
  induction l with
  | nil => simp [reflectionTerms,Count.empty]
  | cons A l ih =>
    intro p hp i hi
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨B,hB,hiB⟩ := ih p hp i hi
      exact ⟨B,List.mem_cons_of_mem _ hB,hiB⟩
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ⟨A,List.mem_cons_self ..,hi⟩
      · obtain ⟨B,hB,hiB⟩ := ih q hq i hi
        exact ⟨B,List.mem_cons_of_mem _ hB,hiB⟩

lemma reflectionTerms_disjoint {N : ℕ} (A : Count N) (l : List (Count N))
    (h : ∀ B ∈ l, Disjoint A.support B.support) (p : ℝ × Count N) (hp : p ∈ reflectionTerms l) :
    Disjoint A.support p.2.support := by
  apply Finset.disjoint_left.mpr
  intro i hiA hip
  obtain ⟨B,hB,hiB⟩ := reflectionTerms_support l p hp i hip
  exact Finset.disjoint_left.mp (h B hB) hiA hiB

lemma reflectionTerms_sum {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum = reflectList l := by
  induction l with
  | nil => simp [reflectionTerms,reflectList]
  | cons A l ih =>
    obtain ⟨ha,hl⟩ := List.pairwise_cons.mp hl
    rw [reflectionTerms,List.map_append,List.sum_append,List.map_map]
    have heq : ((reflectionTerms l).map (fun p => (-2*p.1) • (A.join p.2).zero)) =
        (reflectionTerms l).map (fun p => ((-2:ℝ) • A.zero) * (p.1 • p.2.zero)) := by
      apply List.map_congr_left
      intro p hp
      rw [A.join_zero p.2 (reflectionTerms_disjoint A l ha p hp),smul_mul_smul_comm]
    change ((reflectionTerms l).map (fun p => p.1 • p.2.zero)).sum +
      ((reflectionTerms l).map (fun p => (-2*p.1) • (A.join p.2).zero)).sum = _
    rw [heq,List.sum_map_mul_left,ih hl]
    simp only [reflectList,List.map_cons,List.prod_cons,reflect,sub_mul,one_mul,neg_smul,neg_mul]
    abel

lemma reflectionTerms_weight {N : ℕ} (l : List (Count N)) :
    ((reflectionTerms l).map (fun p => |p.1|)).sum = (3:ℝ)^l.length := by
  induction l with
  | nil => simp [reflectionTerms]
  | cons A l ih =>
    simp only [reflectionTerms,List.map_append,List.sum_append,List.map_map,List.length_cons,pow_succ]
    change ((reflectionTerms l).map (fun p => |p.1|)).sum +
      ((reflectionTerms l).map (fun p => |(-2:ℝ)*p.1|)).sum = _
    simp_rw [abs_mul]
    norm_num only [abs_neg]
    rw [List.sum_map_mul_left,ih]
    ring

lemma star_list_sum {A ι : Type*} [AddMonoid A] [StarAddMonoid A] (l : List ι) (f : ι → A) :
    star (l.map f).sum = (l.map (fun i => star (f i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma reflectList_selfAdjoint {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) :
    star (reflectList l) = reflectList l := by
  rw [← reflectionTerms_sum l hl,star_list_sum]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [star_smul,star_trivial,p.2.zero_projection.isSelfAdjoint.star_eq]


section BilinearBudget
variable {A : Type*} [CStarAlgebra A]

lemma list_sum_sandwich {ι : Type*} (l : List ι) (c : ι → ℝ) (f : ι → A) (L R : A) :
    L * (l.map (fun i => c i • f i)).sum * R =
      (l.map (fun i => c i • (L*f i*R))).sum := by
  simp only [← List.sum_map_mul_left,← List.sum_map_mul_right,mul_smul_comm,smul_mul_assoc]

lemma bilinear_list_bound {ι : Type*} (l : List ι) (c : ι → ℝ) (f : ι → A)
    (H B P : A) (δ : ℝ)
    (h : ∀ i ∈ l, ∀ j ∈ l, ‖H*f i*B*f j*P‖ ≤ δ) :
    ‖H * (l.map (fun i => c i • f i)).sum * B *
      (l.map (fun i => c i • f i)).sum * P‖ ≤ (l.map (fun i => |c i|)).sum^2 * δ := by
  let T := (l.map (fun i => c i • f i)).sum
  let C := (l.map (fun i => |c i|)).sum
  have hj : ∀ i ∈ l, ‖H*f i*B*T*P‖ ≤ C*δ := by
    intro i hi
    rw [show H*f i*B*T*P = (H*f i*B)*T*P by rfl, list_sum_sandwich]
    exact norm_list_smul_sum l c _ δ (h i hi)
  have heq : H*T*B*T*P = (l.map (fun i => c i • (H*f i*B*T*P))).sum := by
    calc
      _ = H*T*(B*T*P) := by simp only [mul_assoc]
      _ = _ := by rw [list_sum_sandwich]; simp only [mul_assoc]
  change ‖H*T*B*T*P‖ ≤ C^2*δ
  rw [heq]
  exact (norm_list_smul_sum l c _ (C*δ) hj).trans_eq (by ring)
end BilinearBudget

lemma reflection_conjugate_expansion {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) (V : Operator N) :
    conjugate V (reflectList l) =
      ((reflectionTerms l).map (fun p => p.1 • conjugate V p.2.zero)).sum := by
  rw [← reflectionTerms_sum l hl,conjugate_list_sum]
  simp only [conjugate_smul]

lemma reflection_transition_bound {N : ℕ} (R : ReflectionLayer N) (V H P : Operator N)
    (A : Count N) (hV : V ∈ unitary (Operator N)) (δ : ℝ)
    (h : ∀ X Y : Count N, ‖H*conjugate V X.zero*conjugate V A.zero*conjugate V Y.zero*P‖ ≤ δ) :
    ‖H*conjugate V (conjugate (reflectionMatrix R) A.zero)*P‖ ≤ (9:ℝ)^R.gates.length*δ := by
  rw [reflectionMatrix_eq]
  unfold conjugate at *
  have heq : H*(V*(reflectList R.gates*A.zero*star (reflectList R.gates))*star V)*P =
      H*conjugate V (reflectList R.gates)*conjugate V A.zero*conjugate V (reflectList R.gates)*P := by
    change H*conjugate V (reflectList R.gates*A.zero*star (reflectList R.gates))*P = _
    rw [reflectList_selfAdjoint _ R.disjoint,conjugate_mul hV,conjugate_mul hV]
    simp only [mul_assoc]
  rw [heq,reflection_conjugate_expansion _ R.disjoint V]
  apply (bilinear_list_bound (reflectionTerms R.gates) Prod.fst
    (fun p => conjugate V p.2.zero) H (conjugate V A.zero) P δ (fun i _ j _ => h i.2 j.2)).trans_eq
  rw [reflectionTerms_weight]
  congr 1
  rw [pow_two,← mul_pow]
  norm_num

lemma small_support_layer_bound {N : ℕ} (V : Operator N) (hV : V ∈ unitary (Operator N))
    (R : ReflectionLayer N) (L : LocalLayer N) (M A : Count N) {r r₁ r₂ δ : ℝ} (hδ : 0 ≤ δ)
    (h₁ : ∀ D : Count N, ‖M.high r₁*conjugate V D.zero*M.zero‖ ≤ δ)
    (h₂ : ∀ D : Count N, ‖M.high r₂*conjugate V D.zero*M.low r₁‖ ≤ δ)
    (h₃ : ∀ D : Count N, ‖M.high r*conjugate V D.zero*M.low r₂‖ ≤ δ) :
    ‖M.high r*conjugate (V*reflectionMatrix R*localMatrix L) A.zero*M.zero‖ ≤
      (9:ℝ)^A.support.card*(3*δ) := by
  have hc : ∀ D : Count N, ‖conjugate V D.zero‖ ≤ 1 := fun D =>
    IsStarProjection.norm_le _ (conjugate_projection hV D.zero_projection)
  have htriple : ∀ X Y Z : Count N,
      ‖M.high r*conjugate V X.zero*conjugate V Y.zero*conjugate V Z.zero*M.zero‖ ≤ 3*δ := by
    intro X Y Z
    exact three_factor_transition _ _ (M.high r₁) (M.high r₂) _ _ _
      (IsStarProjection.norm_le _ (M.high_projection r)) (IsStarProjection.norm_le _ M.zero_projection)
      (IsStarProjection.norm_le _ (M.low_projection r₁)) (hc X) (hc Y) (hc Z) (h₁ Z) (h₂ Y) (h₃ X)
  have hbound := reflection_transition_bound (R.active (A.rotate L)) V (M.high r) M.zero
    (A.rotate L) hV (3*δ) (fun X Y => htriple X (A.rotate L) Y)
  have hlen : (R.active (A.rotate L)).gates.length ≤ A.support.card := R.active_length (A.rotate L)
  calc
    _ = ‖M.high r*conjugate V (conjugate (reflectionMatrix (R.active (A.rotate L))) (A.rotate L).zero)*M.zero‖ := by
      rw [conjugate_comp,conjugate_comp,
        show conjugate (localMatrix L) A.zero = (A.rotate L).zero from (A.rotate_zero L).symm,
        R.active_conjugate]
    _ ≤ (9:ℝ)^(R.active (A.rotate L)).gates.length*(3*δ) := hbound
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) (by positivity)

end QAC

end

end OAI
