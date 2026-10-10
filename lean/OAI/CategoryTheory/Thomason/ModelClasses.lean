import Mathlib
import OAI.CategoryTheory.Thomason.Presentations

namespace OAI

/-! Model Classes. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits HomotopicalAlgebra


end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

variable {J : Type u} [Category.{u} J]

@[ext]
structure LimitCell (F : J ⥤ OmegaCategory.{u}) where
  val : ∀ j, (F.obj j).Cell
  naturality : ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f).map (val i) = val j
  bounded : ∃ n, ∀ j, (F.obj j).source n (val j) = val j

namespace LimitCell

variable (F : J ⥤ OmegaCategory.{u})

def source (k : ℕ) (x : LimitCell F) : LimitCell F where
  val j := (F.obj j).source k (x.val j)
  naturality {i j} f := by rw [(F.map f).map_source, x.naturality f]
  bounded := ⟨k, fun j => (F.obj j).source_source_self k _⟩

def target (k : ℕ) (x : LimitCell F) : LimitCell F where
  val j := (F.obj j).target k (x.val j)
  naturality {i j} f := by rw [(F.map f).map_target, x.naturality f]
  bounded := ⟨k, fun j => (F.obj j).source_target_self k _⟩

lemma composable {k : ℕ} {x y : LimitCell F} (h : target F k x = source F k y) (j : J) :
    (F.obj j).target k (x.val j) = (F.obj j).source k (y.val j) :=
  congrArg (fun z : LimitCell F => z.val j) h

def comp (k : ℕ) (x y : LimitCell F) (h : target F k x = source F k y) : LimitCell F where
  val j := (F.obj j).comp k (x.val j) (y.val j) (composable F h j)
  naturality {i j} f := by
    rw [(F.map f).map_comp k _ _ _ ((F.map f).map_composable (composable F h i))]
    congr 1
    · exact x.naturality f
    · exact y.naturality f
  bounded := by
    rcases x.bounded with ⟨m, hm⟩
    rcases y.bounded with ⟨n, hn⟩
    let l := max (max m n) (k+1)
    have hkl : k < l := lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)
    refine ⟨l, fun j => ?_⟩
    rw [(F.obj j).source_comp_gt l k hkl _ _ _
      ((F.obj j).source_composable hkl (composable F h j))]
    congr 1
    · exact (F.obj j).source_fixed_upwards (le_trans (le_max_left m n) (le_max_left _ _)) (hm j)
    · exact (F.obj j).source_fixed_upwards (le_trans (le_max_right m n) (le_max_left _ _)) (hn j)

end LimitCell

def limitCategory (F : J ⥤ OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := LimitCell F
  source := LimitCell.source F
  target := LimitCell.target F
  comp := LimitCell.comp F
  source_source i j x := by
    apply LimitCell.ext; funext a
    exact (F.obj a).source_source i j (x.val a)
  target_target i j x := by
    apply LimitCell.ext; funext a
    exact (F.obj a).target_target i j (x.val a)
  source_target i j x := by
    apply LimitCell.ext; funext a
    by_cases h : i < j <;>
      simp only [LimitCell.source, LimitCell.target, (F.obj a).source_target, h, ite_true, ite_false]
  target_source i j x := by
    apply LimitCell.ext; funext a
    by_cases h : i < j <;>
      simp only [LimitCell.source, LimitCell.target, (F.obj a).target_source, h, ite_true, ite_false]
  source_comp_le i k hik x y h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).source_comp_le i k hik _ _ _
  target_comp_le i k hik x y h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).target_comp_le i k hik _ _ _
  source_comp_gt i k hki x y h hs := by
    apply LimitCell.ext; funext a
    exact (F.obj a).source_comp_gt i k hki _ _ _ _
  target_comp_gt i k hki x y h ht := by
    apply LimitCell.ext; funext a
    exact (F.obj a).target_comp_gt i k hki _ _ _ _
  unit_left k x h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).unit_left k _ _
  unit_right k x h := by
    apply LimitCell.ext; funext a
    exact (F.obj a).unit_right k _ _
  assoc k x y z hxy hyz hxy_z hx_yz := by
    apply LimitCell.ext; funext a
    exact (F.obj a).assoc k _ _ _ _ _ _ _
  interchange k l hkl a b c d hab hcd hac hbd h₁ h₂ := by
    apply LimitCell.ext; funext j
    exact (F.obj j).interchange k l hkl _ _ _ _ _ _ _ _ _ _
  finite_dimension x := by
    rcases x.bounded with ⟨n, hn⟩
    refine ⟨n, LimitCell.ext ?_⟩
    exact funext hn

def limitProjection (F : J ⥤ OmegaCategory.{u}) (j : J) : Functor (limitCategory F) (F.obj j) where
  map x := x.val j
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

def limitLift (F : J ⥤ OmegaCategory.{u}) (s : Cone F) : Functor s.pt (limitCategory F) where
  map x := {
    val j := (s.π.app j).map x
    naturality {i j} f := congrArg (fun g : Functor s.pt _ => g.map x) (s.w f)
    bounded := by
      rcases s.pt.finite_dimension x with ⟨n, hn⟩
      refine ⟨n, fun j => ?_⟩
      exact ((s.π.app j).map_source n x).symm.trans (congrArg (s.π.app j).map hn) }
  map_source k x := by
    apply LimitCell.ext; funext j
    exact (s.π.app j).map_source k x
  map_target k x := by
    apply LimitCell.ext; funext j
    exact (s.π.app j).map_target k x
  map_comp k x y h h' := by
    apply LimitCell.ext; funext j
    exact (s.π.app j).map_comp k x y h _

def boundedLimitCone (F : J ⥤ OmegaCategory.{u}) : Cone F where
  pt := limitCategory F
  π := {
    app := limitProjection F
    naturality := by
      intro i j f
      apply Functor.ext; funext x
      exact (x.naturality f).symm }

def boundedLimitConeIsLimit (F : J ⥤ OmegaCategory.{u}) : IsLimit (boundedLimitCone F) where
  lift := limitLift F
  fac s j := by
    apply Functor.ext; funext x
    rfl
  uniq s m hm := by
    apply Functor.ext; funext x
    apply LimitCell.ext; funext j
    have h := congrArg (fun g : Functor s.pt (F.obj j) => g.map x) (hm j)
    change (m.map x).val j = ((s.π.app j).map x) at h
    exact h

instance hasLimits : HasLimitsOfSize.{u,u} OmegaCategory.{u} where
  has_limits_of_shape := fun _ _ => {
    has_limit := fun F => ⟨⟨boundedLimitCone F, boundedLimitConeIsLimit F⟩⟩ }

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

noncomputable instance nCategory_hasLimits (n : ℕ) : HasLimitsOfSize.{u,u} (NCategory.{u} n) :=
  hasLimits_of_reflective (nCategoryInclusion n)

noncomputable instance nCategoryInclusion_preservesLimits (n : ℕ) :
    PreservesLimitsOfSize.{v,w} (nCategoryInclusion.{u} n) :=
  (truncationAdjunction n).rightAdjoint_preservesLimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

lemma faces_zero {D : Type v} {M : Type w} [AddCommGroup M] (l : List D) :
    faces (fun _ => (0 : M)) l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [faces_cons, zero_sub, neg_eq_zero] using ih

def awZeroWord (l : List E) : Chains E :=
  if ∀ a ∈ l, θ a = 0 then bracket l else 0

def awEdgeWord (l : List E) : Chains E :=
  match l.reverse with
  | [] => 0
  | a :: r => if θ a = 0 then 0 else awZeroWord θ r.reverse

@[simp] lemma awEdgeWord_nil : awEdgeWord θ [] = 0 := rfl

lemma awEdgeWord_append (l : List E) (a : E) :
    awEdgeWord θ (l ++ [a]) = if θ a = 0 then 0 else awZeroWord θ l := by
  simp [awEdgeWord]

lemma awZeroWord_of_all {l : List E} (h : ∀ a ∈ l, θ a = 0) :
    awZeroWord θ l = bracket l := ite_eq_left h

lemma awZeroWord_of_not_all {l : List E} (h : ¬∀ a ∈ l, θ a = 0) :
    awZeroWord θ l = 0 := ite_eq_right h

lemma awZeroWord_append_of_ne (l : List E) {a : E} (ha : θ a ≠ 0) :
    awZeroWord θ (l ++ [a]) = 0 := by
  apply awZeroWord_of_not_all
  intro h
  exact ha (h a (by simp))

lemma all_zero_of_last_zero {l : List E} {a : E}
    (h : (l ++ [a]).Pairwise (· ≤ ·)) (ha : θ a = 0) :
    ∀ b ∈ l ++ [a], θ b = 0 := by
  intro b hb
  have hba : b ≤ a := by simpa using h.rel_getLast hb
  exact le_antisymm (by simpa [ha] using θ.monotone hba) (Fin.zero_le _)

lemma awEdgeWord_of_all {l : List E} (h : ∀ a ∈ l, θ a = 0) :
    awEdgeWord θ l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a => rw [awEdgeWord_append, ite_eq_left (h a (by simp))]

lemma boundary_awZeroWord {l : List E} {a : E}
    (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    boundary (awZeroWord θ (l ++ [a])) =
      faces (awZeroWord θ) (l ++ [a]) -
        ((-1 : ℤ)^l.length) • awEdgeWord θ (l ++ [a]) := by
  by_cases ha : θ a = 0
  · have hall := all_zero_of_last_zero θ h ha
    rw [awZeroWord_of_all θ hall, awEdgeWord_of_all θ hall, smul_zero, sub_zero,
      boundary_bracket h, ← faces_bracket]
    apply faces_congr
    intro m hm
    exact (awZeroWord_of_all θ (fun b hb => hall b (hm.subset hb))).symm
  · rw [awZeroWord_append_of_ne θ l ha, map_zero, awEdgeWord_append,
      ite_eq_right ha, faces_append_singleton]
    have hz : faces (fun m => awZeroWord θ (m ++ [a])) l = 0 := by
      have he : (fun m : List E => awZeroWord θ (m ++ [a])) = fun _ => 0 := by
        funext m
        exact awZeroWord_append_of_ne θ m ha
      rw [he, faces_zero]
    rw [hz, zero_add, sub_self]

lemma boundary_awEdgeWord {l : List E} (h : l.Pairwise (· ≤ ·)) :
    boundary (awEdgeWord θ l) = faces (awEdgeWord θ) l := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a =>
    by_cases ha : θ a = 0
    · have hall := all_zero_of_last_zero θ h ha
      rw [awEdgeWord_of_all θ hall, map_zero]
      have he : faces (awEdgeWord θ) (l ++ [a]) = faces (fun _ => 0) (l ++ [a]) := by
        apply faces_congr
        intro m hm
        exact awEdgeWord_of_all θ (fun b hb => hall b (hm.subset hb))
      rw [he, faces_zero]
    · rw [awEdgeWord_append, ite_eq_right ha, faces_append_singleton]
      have he : faces (fun m => awEdgeWord θ (m ++ [a])) l =
          faces (awZeroWord θ) l := by
        apply faces_congr
        intro m _
        rw [awEdgeWord_append, ite_eq_right ha]
      rw [he]
      cases l using List.reverseRecOn with
      | nil =>
        rw [awZeroWord_of_all θ (by simp), boundary_bracket (by simp)]
        simp only [wordBoundary_nil, faces_nil, List.length_nil, pow_zero,
          one_smul, awEdgeWord_nil, add_zero]
      | append_singleton k b =>
        rw [boundary_awZeroWord θ (List.pairwise_append.mp h).1,
          List.length_append, List.length_singleton, pow_succ, mul_neg, mul_one,
          neg_smul, sub_eq_add_neg]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

def awZero : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun w : Word E => awZeroWord θ w.val)

def awEdge : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun w : Word E => awEdgeWord θ w.val)

lemma awZeroWord_eq_zero_of_not_pairwise {l : List E}
    (h : ¬l.Pairwise (· < ·)) : awZeroWord θ l = 0 := by
  unfold awZeroWord
  split <;> simp [bracket_of_not_pairwise h]

lemma awEdgeWord_eq_zero_of_not_pairwise {l : List E}
    (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : awEdgeWord θ l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a =>
    rw [awEdgeWord_append]
    split
    · rfl
    next ha =>
      by_cases hall : ∀ b ∈ l, θ b = 0
      · rw [awZeroWord_of_all θ hall]
        apply bracket_of_not_pairwise
        intro hl
        apply hn
        apply List.pairwise_append.mpr
        refine ⟨hl, by simp, ?_⟩
        intro b hb c hc
        simp only [List.mem_singleton] at hc
        subst c
        apply lt_of_le_of_ne ((List.pairwise_append.mp h).2.2 b hb a (by simp))
        intro hba
        exact ha (by simpa [hba] using hall b hb)
      · exact awZeroWord_of_not_all θ hall

lemma awZero_bracket (l : List E) : awZero θ (bracket l) = awZeroWord θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun w : Word E => awZeroWord θ w.val)
      (Finsupp.single ⟨l, hs⟩ 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, awZeroWord_eq_zero_of_not_pairwise θ hs]

lemma awEdge_bracket {l : List E} (h : l.Pairwise (· ≤ ·)) :
    awEdge θ (bracket l) = awEdgeWord θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun w : Word E => awEdgeWord θ w.val)
      (Finsupp.single ⟨l, hs⟩ 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, awEdgeWord_eq_zero_of_not_pairwise θ h hs]

lemma awZero_wordBoundary (l : List E) :
    awZero θ (wordBoundary l) = faces (awZeroWord θ) l := by
  rw [← faces_bracket]
  change (awZero θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m _
  exact awZero_bracket θ m

lemma awEdge_wordBoundary {l : List E} (h : l.Pairwise (· ≤ ·)) :
    awEdge θ (wordBoundary l) = faces (awEdgeWord θ) l := by
  rw [← faces_bracket]
  change (awEdge θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact awEdge_bracket θ (h.sublist hm)

lemma awEdge_boundary (c : Chains E) :
    boundary (awEdge θ c) = awEdge θ (boundary c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    have hl := l.property.imp fun h => le_of_lt h
    rw [awEdge_bracket θ hl, boundary_bracket hl, awEdge_wordBoundary θ hl,
      boundary_awEdgeWord θ hl]

lemma awZeroWord_positive (l : List E) : Positive (awZeroWord θ l) := by
  unfold awZeroWord
  split
  · exact bracket_positive l
  · exact fun _ => le_rfl

lemma awEdgeWord_positive (l : List E) : Positive (awEdgeWord θ l) := by
  cases l using List.reverseRecOn with
  | nil => exact fun _ => le_rfl
  | append_singleton l a =>
    rw [awEdgeWord_append]
    split
    · exact fun _ => le_rfl
    · exact awZeroWord_positive θ l

lemma awZero_positive {c : Chains E} (hc : Positive c) : Positive (awZero θ c) :=
  linearCombination_positive _ (fun w => awZeroWord_positive θ w.val) hc

lemma awEdge_positive {c : Chains E} (hc : Positive c) : Positive (awEdge θ c) :=
  linearCombination_positive _ (fun w => awEdgeWord_positive θ w.val) hc

lemma awOne_positive {c : Chains E} (hc : Positive c) : Positive (c - awZero θ c) := by
  classical
  have he : ((LinearMap.id : Chains E →ₗ[ℤ] Chains E) - awZero θ) =
      Finsupp.linearCombination ℤ (fun w : Word E =>
        if ∀ a ∈ w.val, θ a = 0 then 0 else bracket w.val) := by
    apply Finsupp.lhom_ext
    intro w z
    simp only [LinearMap.sub_apply, LinearMap.id_apply, awZero,
      Finsupp.linearCombination_single]
    have hw : Finsupp.single w z = z • bracket w.val := by
      rw [bracket_of_pairwise w.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hw]
    unfold awZeroWord
    split <;> simp
  change Positive (((LinearMap.id : Chains E →ₗ[ℤ] Chains E) - awZero θ) c)
  rw [he]
  apply linearCombination_positive _ _ hc
  intro w
  split
  · exact fun _ => le_rfl
  · exact bracket_positive w.val

lemma awZeroWord_mem_grade (l : List E) : awZeroWord θ l ∈ grade l.length := by
  unfold awZeroWord
  split
  · exact bracket_mem_grade l
  · exact Submodule.zero_mem _

lemma awEdgeWord_mem_grade (l : List E) : awEdgeWord θ l ∈ grade (l.length - 1) := by
  cases l using List.reverseRecOn with
  | nil => exact Submodule.zero_mem _
  | append_singleton l a =>
    rw [awEdgeWord_append]
    split
    · exact Submodule.zero_mem _
    · simpa using awZeroWord_mem_grade θ l

lemma awZero_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    awZero θ c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [hw] using awZeroWord_mem_grade θ w.val

lemma awEdge_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade (k+1)) :
    awEdge θ c ∈ grade k := by
  apply linearCombination_mem_grade _ (k+1) k _ hc
  intro w hw
  simpa only [hw, Nat.add_sub_cancel] using awEdgeWord_mem_grade θ w.val

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

lemma boundary_awZero (c : Chains E) :
    boundary (awZero θ c) = awZero θ (boundary c) - awEdge θ (degreeSign c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    have hw : boundary (awZero θ (bracket l.val)) =
        awZero θ (boundary (bracket l.val)) - awEdge θ (degreeSign (bracket l.val)) := by
      have hl := l.property.imp fun h => le_of_lt h
      rw [awZero_bracket, boundary_bracket hl, awZero_wordBoundary,
        degreeSign_bracket, map_smul, awEdge_bracket θ hl]
      rcases l with ⟨l, hls⟩
      cases l using List.reverseRecOn with
      | nil =>
        rw [awZeroWord_of_all θ (by simp), boundary_bracket (by simp)]
        simp only [wordBoundary_nil, faces_nil, awEdgeWord_nil, smul_zero, sub_zero]
      | append_singleton l a =>
        simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
          using boundary_awZeroWord θ hl
    rw [hw, smul_sub]
    abel

lemma boundary_awZero_of_grade {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+1)) :
    boundary (awZero θ c) = awZero θ (boundary c) - ((-1 : ℤ)^p) • awEdge θ c := by
  rw [boundary_awZero, degreeSign_of_grade hc, map_smul]

def awMap : (p : ℕ) → (complex E).Chain p →+
    (complex E).cylinder.Chain p
  | 0 =>
    { toFun := fun c => (⟨awZero θ c.val, awZero_mem_grade θ c.property⟩,
        c - ⟨awZero θ c.val, awZero_mem_grade θ c.property⟩)
      map_zero' := by
        apply Prod.ext
        · apply Subtype.ext; exact map_zero _
        · apply Subtype.ext
          change (0 : Chains E) - awZero θ 0 = 0
          simp
      map_add' := by
        intro x y
        apply Prod.ext
        · apply Subtype.ext; exact map_add _ _ _
        · apply Subtype.ext
          change x.val + y.val - awZero θ (x.val + y.val) =
            (x.val - awZero θ x.val) + (y.val - awZero θ y.val)
          rw [map_add]; abel }
  | p+1 =>
    { toFun := fun c => (⟨awZero θ c.val, awZero_mem_grade θ c.property⟩,
        c - ⟨awZero θ c.val, awZero_mem_grade θ c.property⟩,
        ⟨awEdge θ c.val, awEdge_mem_grade θ c.property⟩)
      map_zero' := by
        apply Prod.ext
        · apply Subtype.ext; exact map_zero _
        · apply Prod.ext
          · apply Subtype.ext
            change (0 : Chains E) - awZero θ 0 = 0
            simp
          · apply Subtype.ext; exact map_zero _
      map_add' := by
        intro x y
        apply Prod.ext
        · apply Subtype.ext; exact map_add _ _ _
        · apply Prod.ext
          · apply Subtype.ext
            change x.val + y.val - awZero θ (x.val + y.val) =
              (x.val - awZero θ x.val) + (y.val - awZero θ y.val)
            rw [map_add]; abel
          · apply Subtype.ext; exact map_add _ _ _ }

def awHom : DirectedComplex.Hom (complex E) (complex E).cylinder where
  map := awMap θ
  map_d p c := by
    symm
    cases p with
    | zero =>
      apply Prod.ext <;> apply Subtype.ext
      · change (boundary (awZero θ c.val) - awEdge θ c.val) = awZero θ (boundary c.val)
        rw [boundary_awZero_of_grade θ c.property]
        norm_num
      · change boundary (c.val - awZero θ c.val) + awEdge θ c.val =
          boundary c.val - awZero θ (boundary c.val)
        rw [map_sub, boundary_awZero_of_grade θ c.property]
        norm_num
        abel
    | succ p =>
      apply Prod.ext
      · apply Subtype.ext
        change boundary (awZero θ c.val) - ((-1 : ℤ)^(p+1)) • awEdge θ c.val =
          awZero θ (boundary c.val)
        rw [boundary_awZero_of_grade θ c.property, pow_succ]
        simp only [mul_neg, mul_one, neg_smul]
        abel
      · apply Prod.ext
        · apply Subtype.ext
          change boundary (c.val - awZero θ c.val) + ((-1 : ℤ)^(p+1)) • awEdge θ c.val =
            boundary c.val - awZero θ (boundary c.val)
          rw [map_sub, boundary_awZero_of_grade θ c.property, pow_succ]
          simp only [mul_neg, mul_one, neg_smul]
          abel
        · exact Subtype.ext (awEdge_boundary θ c.val)
  map_augmentation c := by
    change emptyCoefficient (boundary (awZero θ c.val)) +
      emptyCoefficient (boundary (c.val - awZero θ c.val)) =
      emptyCoefficient (boundary c.val)
    simp only [map_sub]
    abel
  map_positive p c hc := by
    cases p with
    | zero => exact ⟨awZero_positive θ hc, awOne_positive θ hc⟩
    | succ p => exact ⟨awZero_positive θ hc, awOne_positive θ hc, awEdge_positive θ hc⟩

end Thomason.NormalizedChains

end

end OAI
