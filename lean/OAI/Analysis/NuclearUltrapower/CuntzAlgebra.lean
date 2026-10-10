import OAI.Analysis.NuclearUltrapower.Model
import OAI.Analysis.NuclearUltrapower.HilbertInduction
import OAI.Analysis.NuclearUltrapower.FullGroupAlgebra

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzModel

abbrev Index := ℤ × ℕ
abbrev Space := L2 Index
local instance : DecidableEq Index := Classical.decEq _

/-- Integer height separates words of different lengths; the binary coordinate
partitions every level into the two isometric ranges. -/
def shiftIndex (i : Fin 2) : Index ↪ Index where
  toFun x := (x.1 + 1, 2*x.2+i.val)
  inj' := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    congr 1 <;> omega

@[simp] theorem shiftIndex_apply (i : Fin 2) (x : Index) :
    shiftIndex i x = (x.1+1,2*x.2+i.val) := rfl

theorem shiftIndex_disjoint {i j : Fin 2} (hij : i ≠ j) (x y : Index) :
    shiftIndex i x ≠ shiftIndex j y := by
  intro h
  have hh := congrArg Prod.snd h
  dsimp at hh
  have hi := i.isLt
  have hj := j.isLt
  apply hij
  apply Fin.ext
  omega

theorem shiftIndex_surjective (x : Index) : ∃ i y, shiftIndex i y = x := by
  refine ⟨⟨x.2 % 2, Nat.mod_lt _ (by decide)⟩, (x.1-1,x.2/2), ?_⟩
  apply Prod.ext <;> simp only [shiftIndex_apply] <;> omega

def shift (i : Fin 2) : Space →L[ℂ] Space := (l2Embedding (shiftIndex i)).toContinuousLinearMap

@[simp] theorem shift_single (i : Fin 2) (x : Index) (c : ℂ) :
    shift i (lp.single 2 x c) = lp.single 2 (shiftIndex i x) c :=
  by simpa only [shift, LinearIsometry.coe_toContinuousLinearMap] using
    l2Embedding_single (shiftIndex i) x c

@[simp] theorem shift_adjoint_apply (i : Fin 2) (x : Space) (k : Index) :
    (shift i).adjoint x k = x (shiftIndex i k) := l2Embedding_adjoint_apply _ _ _

@[simp] theorem shift_adjoint_single_same (i : Fin 2) (x : Index) (c : ℂ) :
    (shift i).adjoint (lp.single 2 (shiftIndex i x) c) = lp.single 2 x c := by
  ext y
  simp only [shift_adjoint_apply, lp.single_apply, Pi.single_apply,
    (shiftIndex i).injective.eq_iff]

@[simp] theorem shift_adjoint_single_ne {i j : Fin 2} (hij : i ≠ j) (x : Index) (c : ℂ) :
    (shift i).adjoint (lp.single 2 (shiftIndex j x) c) = 0 := by
  ext y
  rw [shift_adjoint_apply]
  change (lp.single (E := fun _ : Index => ℂ) 2 (shiftIndex j x) c) (shiftIndex i y) = 0
  exact lp.single_apply_ne 2 _ _ (shiftIndex_disjoint hij y x)

theorem relations : CuntzTwoRelations shift := by
  constructor
  · intro i
    change (shift i).adjoint.comp (shift i) = 1
    exact (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp
      (l2Embedding (shiftIndex i)).isometry
  · apply l2_clm_ext
    intro x c
    obtain ⟨j,y,rfl⟩ := shiftIndex_surjective x
    simp only [sum_apply, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, one_apply_eq_self]
    rw [Finset.sum_eq_single j]
    · simp only [shift_adjoint_single_same, shift_single]
    · intro i _ hij
      rw [shift_adjoint_single_ne hij y c, map_zero]
    · simp

instance : Nontrivial Space := by
  refine ⟨⟨lp.single 2 (0,0) (1:ℂ), 0, ?_⟩⟩
  intro h
  have := congrArg (fun x : Space => x (0,0)) h
  simp at this

end NuclearUltrapower.CuntzModel
end
end

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.CuntzPolynomial
abbrev Letter := Fin 2 × Bool
abbrev Word := FreeMonoid Letter

def flip (a : Letter) : Letter := (a.1,!a.2)
@[simp] theorem flip_flip (a : Letter) : flip (flip a) = a := by
  rcases a with ⟨i,b⟩
  cases b <;> rfl

instance : Star Word := ⟨fun w => FreeMonoid.ofList ((FreeMonoid.toList w).reverse.map flip)⟩
@[simp] theorem star_word_of (a : Letter) : star (FreeMonoid.of a) = FreeMonoid.of (flip a) := rfl
instance : InvolutiveStar Word where
  star_involutive w := by
    apply FreeMonoid.toList.injective
    change ((FreeMonoid.toList w).reverse.map flip).reverse.map flip = FreeMonoid.toList w
    simp [List.map_reverse, List.map_map, Function.comp_def]
instance : StarMul Word where
  star_mul w v := by
    apply FreeMonoid.toList.injective
    change ((FreeMonoid.toList w ++ FreeMonoid.toList v).reverse.map flip) =
      (FreeMonoid.toList v).reverse.map flip ++ (FreeMonoid.toList w).reverse.map flip
    simp

abbrev Poly := ℂ[Word]

def involutionAdd : Poly →+ Poly :=
  MonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapDomain.addMonoidHom (star : Word → Word)).comp
      ((Finsupp.mapRange.addMonoidHom (starAddEquiv : ℂ ≃+ ℂ).toAddMonoidHom).comp
        MonoidAlgebra.coeffAddEquiv.toAddMonoidHom))
instance : Star Poly := ⟨involutionAdd⟩
@[simp] theorem star_single (w : Word) (c : ℂ) :
    star (MonoidAlgebra.single w c) = MonoidAlgebra.single (star w) (star c) := by
  change involutionAdd _ = _
  simp [involutionAdd]
instance : InvolutiveStar Poly where
  star_involutive x := by
    have h : involutionAdd.comp involutionAdd = AddMonoidHom.id _ := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro w c
      change star (star (MonoidAlgebra.single w c)) = MonoidAlgebra.single w c
      simp only [star_single, star_star]
    exact congrArg (fun f : Poly →+ Poly => f x) h
instance : StarAddMonoid Poly where
  star_add := involutionAdd.map_add
instance : StarModule ℂ Poly where
  star_smul c x := by
    let f : Poly →+ Poly := involutionAdd.comp (DistribSMul.toAddMonoidHom Poly c)
    let g : Poly →+ Poly := (DistribSMul.toAddMonoidHom Poly (star c)).comp involutionAdd
    have h : f = g := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro a b
      change star (c • MonoidAlgebra.single a b) = star c • star (MonoidAlgebra.single a b)
      simp only [MonoidAlgebra.smul_single, star_single, star_mul, smul_eq_mul, mul_comm]
    exact congrArg (fun f : Poly →+ Poly => f x) h
instance : StarRing Poly where
  star_add := involutionAdd.map_add
  star_mul x y := by
    induction x using MonoidAlgebra.induction_on with
    | of a =>
      induction y using MonoidAlgebra.induction_on with
      | of b => simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          one_mul, star_single, star_one, star_mul]
      | add y z hy hz => simp only [mul_add, star_add, hy, hz, add_mul]
      | smul c y hy => simp only [mul_smul_comm, star_smul, hy, smul_mul_assoc]
    | add x z hx hz => simp only [add_mul, star_add, hx, hz, mul_add]
    | smul c x hx => simp only [smul_mul_assoc, star_smul, hx, mul_smul_comm]

variable {D : Type*} [CStarAlgebra D]
def evalLetter (r : Fin 2 → D) (a : Letter) : D := if a.2 then star (r a.1) else r a.1
@[simp] theorem evalLetter_flip (r : Fin 2 → D) (a : Letter) :
    evalLetter r (flip a) = star (evalLetter r a) := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [evalLetter, flip]

def evalWord (r : Fin 2 → D) : Word →* D := FreeMonoid.lift (evalLetter r)
@[simp] theorem evalWord_of (r : Fin 2 → D) (a : Letter) :
    evalWord r (FreeMonoid.of a) = evalLetter r a := rfl
@[simp] theorem evalWord_star (r : Fin 2 → D) (w : Word) :
    evalWord r (star w) = star (evalWord r w) := by
  induction w using FreeMonoid.recOn with
  | one => simp
  | of_mul a w ih => simp only [star_mul, star_word_of, map_mul, evalWord_of, evalLetter_flip, ih]

def evaluate (r : Fin 2 → D) : Poly →⋆ₐ[ℂ] D where
  __ := MonoidAlgebra.lift ℂ D Word (evalWord r)
  map_star' x := by
    change (MonoidAlgebra.lift ℂ D Word (evalWord r)) (star x) =
      star ((MonoidAlgebra.lift ℂ D Word (evalWord r)) x)
    induction x using MonoidAlgebra.induction_on with
    | of w => simp only [MonoidAlgebra.of_apply,star_single,star_one,
        MonoidAlgebra.lift_single,one_smul,evalWord_star]
    | add x y hx hy => simp only [star_add,map_add,hx,hy]
    | smul c x hx => simp only [star_smul,map_smul,hx]
@[simp] theorem evaluate_single (r : Fin 2 → D) (w : Word) (c : ℂ) :
    evaluate r (MonoidAlgebra.single w c) = c • evalWord r w :=
  MonoidAlgebra.lift_single _ _ _

def generator (i : Fin 2) : Poly := MonoidAlgebra.single (FreeMonoid.of (i,false)) 1
@[simp] theorem evaluate_generator (r : Fin 2 → D) (i : Fin 2) : evaluate r (generator i) = r i := by
  simp [generator,evalLetter]

theorem evalLetter_norm_le (r : Fin 2 → D) (hr : CuntzTwoRelations r) (a : Letter) :
    ‖evalLetter r a‖ ≤ 1 := by
  have hh : ‖r a.1‖ * ‖r a.1‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, hr.1]
    cases subsingleton_or_nontrivial D with
    | inl h => simp [Subsingleton.elim (1 : D) 0]
    | inr h => simp
  have h : ‖r a.1‖ ≤ 1 := by nlinarith [norm_nonneg (r a.1)]
  simp only [evalLetter]
  split_ifs <;> simpa only [norm_star] using h

theorem evalWord_norm_le (r : Fin 2 → D) (hr : CuntzTwoRelations r) (w : Word) :
    ‖evalWord r w‖ ≤ 1 := by
  induction w using FreeMonoid.recOn with
  | one =>
    rw [map_one]
    cases subsingleton_or_nontrivial D with
    | inl h => simp [Subsingleton.elim (1 : D) 0]
    | inr h => simp
  | of_mul a w ih =>
    rw [map_mul, evalWord_of]
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (evalLetter_norm_le r hr a)).trans ih)

end NuclearUltrapower.CuntzPolynomial
end
end

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.CuntzPolynomial

/-- The possible operator norms in all unital models of the Cuntz relations. -/
def modelNormSet (x : Poly) : Set ℝ :=
  {t | ∃ (D : Type) (_ : CStarAlgebra D) (ρ : Fin 2 → D) (_ : CuntzTwoRelations ρ), t = ‖evaluate ρ x‖}

theorem modelNormSet_nonempty (x : Poly) : (modelNormSet x).Nonempty := by
  exact ⟨‖evaluate CuntzModel.shift x‖, CuntzModel.Space →L[ℂ] CuntzModel.Space,
    inferInstance, CuntzModel.shift, CuntzModel.relations, rfl⟩

/-- Every finite star-polynomial is bounded uniformly over ALL models. -/
theorem models_bounded (x : Poly) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (D : Type) [CStarAlgebra D] (ρ : Fin 2 → D) (_ : CuntzTwoRelations ρ), ‖evaluate ρ x‖ ≤ M := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨1, zero_le_one, ?_⟩
    intro D _ ρ hρ
    simp only [MonoidAlgebra.of_apply, evaluate_single, one_smul]
    exact evalWord_norm_le ρ hρ g
  | add x y hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M+N, add_nonneg hM hN, ?_⟩
    intro D _ ρ hρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hx D ρ hρ) (hy D ρ hρ))
  | smul c x hx =>
    obtain ⟨M, hM, hx⟩ := hx
    refine ⟨‖c‖*M, mul_nonneg (norm_nonneg _) hM, ?_⟩
    intro D _ ρ hρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hx D ρ hρ) (norm_nonneg _)

theorem modelNormSet_bdd (x : Poly) : BddAbove (modelNormSet x) := by
  obtain ⟨M, _, hx⟩ := models_bounded x
  refine ⟨M, ?_⟩
  rintro r ⟨D, inst, ρ, hρ, rfl⟩
  exact hx D ρ hρ

/-- The universal C*-seminorm over all Cuntz models. -/
def universalNorm (x : Poly) : ℝ := sSup (modelNormSet x)

theorem model_norm_le (x : Poly) (D : Type) [CStarAlgebra D] (ρ : Fin 2 → D) (hρ : CuntzTwoRelations ρ) :
    ‖evaluate ρ x‖ ≤ universalNorm x :=
  le_csSup (modelNormSet_bdd x) ⟨D, inferInstance, ρ, hρ, rfl⟩

theorem universalNorm_le {x : Poly} {M : ℝ}
    (h : ∀ (D : Type) [CStarAlgebra D] (ρ : Fin 2 → D) (_ : CuntzTwoRelations ρ), ‖evaluate ρ x‖ ≤ M) :
    universalNorm x ≤ M := by
  apply csSup_le (modelNormSet_nonempty x)
  rintro r ⟨D, inst, ρ, hρ, rfl⟩
  exact h D ρ hρ

theorem universalNorm_nonneg (x : Poly) : 0 ≤ universalNorm x :=
  (norm_nonneg _).trans (model_norm_le x (CuntzModel.Space →L[ℂ] CuntzModel.Space)
    CuntzModel.shift CuntzModel.relations)

@[simp] theorem universalNorm_zero : universalNorm (0 : Poly) = 0 := by
  apply le_antisymm _ (universalNorm_nonneg _)
  apply universalNorm_le
  intro D _ ρ hρ
  simp

/-- The universal model supremum is a submultiplicative seminorm. -/
def universalSeminorm : RingSeminorm Poly where
  toFun := universalNorm
  map_zero' := universalNorm_zero
  add_le' x y := by
    apply universalNorm_le
    intro D _ ρ hρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (model_norm_le x D ρ hρ) (model_norm_le y D ρ hρ))
  neg' x := by
    apply le_antisymm
    · apply universalNorm_le
      intro D _ ρ hρ
      simpa only [map_neg, norm_neg] using model_norm_le x D ρ hρ
    · have h : universalNorm x ≤ universalNorm (-x) := by
        apply universalNorm_le
        intro D _ ρ hρ
        have := model_norm_le (-x) D ρ hρ
        simpa only [map_neg, norm_neg] using this
      exact h
  mul_le' x y := by
    apply universalNorm_le
    intro D _ ρ hρ
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (model_norm_le x D ρ hρ) (model_norm_le y D ρ hρ)
      (norm_nonneg _) (universalNorm_nonneg _))

instance : SeminormedRing Poly := universalSeminorm.toSeminormedRing

@[simp] theorem norm_eq_universalNorm (x : Poly) : ‖x‖ = universalNorm x := rfl

instance : NormedStarGroup Poly where
  norm_star_le x := by
    apply universalNorm_le
    intro D _ ρ hρ
    simpa only [map_star, norm_star, norm_eq_universalNorm] using model_norm_le x D ρ hρ

instance : NormedAlgebra ℂ Poly where
  norm_smul_le c x := by
    apply universalNorm_le
    intro D _ ρ hρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (model_norm_le x D ρ hρ) (norm_nonneg _)

/-- C*-identity at the seminorm level, which survives separated completion. -/
theorem norm_mul_self_le (x : Poly) : ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  have h : ‖x‖ ≤ Real.sqrt ‖star x * x‖ := by
    apply universalNorm_le
    intro D _ ρ hρ
    apply (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mpr
    have hm := model_norm_le (star x*x) D ρ hρ
    simpa only [map_mul, map_star, CStarRing.norm_star_mul_self, pow_two, norm_eq_universalNorm] using hm
  nlinarith [Real.sq_sqrt (norm_nonneg (star x*x)), norm_nonneg x]

/-- Every model evaluation is contractive for the universal seminorm. -/
theorem evaluate_continuous {D : Type} [CStarAlgebra D] (ρ : Fin 2 → D) (hρ : CuntzTwoRelations ρ) :
    Continuous (evaluate ρ) := by
  apply (evaluate ρ).toLinearMap.mkContinuous 1 ?_ |>.continuous
  intro x
  change ‖evaluate ρ x‖ ≤ 1 * universalNorm x
  simpa only [one_mul] using model_norm_le x D ρ hρ

end NuclearUltrapower.CuntzPolynomial

namespace NuclearUltrapower.CuntzUniversal
open UniformSpace CuntzPolynomial

/-- The universal completion is separated; Cuntz relations vanish in its norm. -/
def Algebra := Completion Poly
instance : CStarAlgebra Algebra := UniversalCompletion.cstarAlgebra norm_mul_self_le

def inclusion : Poly →⋆ₐ[ℂ] Algebra := UniversalCompletion.inclusion
def generator (i : Fin 2) : Algebra := inclusion (CuntzPolynomial.generator i)

def modelMap {D : Type} [CStarAlgebra D] (r : Fin 2 → D) (hr : CuntzTwoRelations r) :
    Algebra →⋆ₐ[ℂ] D := UniversalCompletion.extend (evaluate r) (evaluate_continuous r hr)

@[simp] theorem modelMap_coe {D : Type} [CStarAlgebra D] (r : Fin 2 → D)
    (hr : CuntzTwoRelations r) (x : Poly) : modelMap r hr (inclusion x) = evaluate r x :=
  UniversalCompletion.extend_coe _ _ _

@[simp] theorem modelMap_generator {D : Type} [CStarAlgebra D] (r : Fin 2 → D)
    (hr : CuntzTwoRelations r) (i : Fin 2) : modelMap r hr (generator i) = r i := by
  rw [generator,modelMap_coe,evaluate_generator]

/-- Seminorm-zero relations become literal equalities in the separated completion. -/
theorem inclusion_eq_of_models (x y : Poly)
    (h : ∀ (D : Type) [CStarAlgebra D] (r : Fin 2 → D), CuntzTwoRelations r →
      evaluate r x = evaluate r y) : inclusion x = inclusion y := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← map_sub]
  change ‖((x-y : Poly) : Completion Poly)‖ = 0
  rw [Completion.norm_coe]
  apply le_antisymm _ (norm_nonneg _)
  apply universalNorm_le
  intro D _ r hr
  rw [map_sub,h D r hr,sub_self,norm_zero]

theorem relations : CuntzTwoRelations generator := by
  constructor
  · intro i
    change star (inclusion (CuntzPolynomial.generator i)) * inclusion _ = 1
    rw [← map_star, ← map_mul, ← map_one inclusion]
    apply inclusion_eq_of_models
    intro D _ r hr
    simpa only [map_mul,map_star,map_one,evaluate_generator] using hr.1 i
  · change ∑ i, inclusion (CuntzPolynomial.generator i) * star (inclusion _) = 1
    simp only [← map_star, ← map_mul, ← map_sum]
    rw [← map_one inclusion]
    apply inclusion_eq_of_models
    intro D _ r hr
    simpa only [map_sum,map_mul,map_star,map_one,evaluate_generator] using hr.2

instance : Nontrivial Algebra := by
  apply nontrivial_of_ne (0 : Algebra) 1
  intro h
  have hh := congrArg (modelMap CuntzModel.shift CuntzModel.relations) h
  exact zero_ne_one (by simpa only [map_zero,map_one] using hh)

/-- Values on the two generators determine all continuous model maps. -/
theorem modelMap_unique {D : Type} [CStarAlgebra D] (r : Fin 2 → D)
    (hr : CuntzTwoRelations r) (φ : Algebra →⋆ₐ[ℂ] D)
    (hφ : ∀ i, φ (generator i) = r i) : φ = modelMap r hr := by
  have hletter (a : Letter) : φ (inclusion (MonoidAlgebra.of ℂ Word (FreeMonoid.of a))) =
      evalLetter r a := by
    rcases a with ⟨i,b⟩
    cases b
    · exact hφ i
    · change φ (inclusion (MonoidAlgebra.single (FreeMonoid.of (i,true)) 1)) = star (r i)
      have hg : (MonoidAlgebra.single (FreeMonoid.of (i,true)) 1 : Poly) =
          star (CuntzPolynomial.generator i) := by
        rw [CuntzPolynomial.generator,star_single,star_word_of,star_one]
        rfl
      rw [hg,map_star,map_star]
      exact congrArg star (hφ i)
  have hw (w : Word) : φ (inclusion (MonoidAlgebra.of ℂ Word w)) = evalWord r w := by
    induction w using FreeMonoid.recOn with
    | one =>
      change φ (inclusion 1) = evalWord r 1
      simp only [map_one]
    | of_mul a w ih => simp only [map_mul,hletter,ih,evalWord_of]
  have he (x : Poly) : φ (inclusion x) = modelMap r hr (inclusion x) := by
    rw [modelMap_coe]
    induction x using MonoidAlgebra.induction_on with
    | of w => simpa only [MonoidAlgebra.of_apply,evaluate_single,one_smul] using hw w
    | add x y hx hy => simp only [map_add,hx,hy]
    | smul c x hx => simp only [map_smul,hx]
  have hc (f : Algebra →⋆ₐ[ℂ] D) : Continuous f :=
    AddMonoidHomClass.continuous_of_bound f 1 (fun x => by
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le f x)
  apply DFunLike.ext'
  exact Completion.denseRange_coe.equalizer (hc φ) (hc (modelMap r hr)) (funext he)

def bundled : UnitalCStar := ⟨Algebra⟩

theorem universal : IsCuntzTwoAlgebra bundled generator := by
  refine ⟨relations, ?_⟩
  intro D r hr
  exact ⟨modelMap r hr, modelMap_generator r hr, fun φ hφ => modelMap_unique r hr φ hφ⟩

end NuclearUltrapower.CuntzUniversal
end
end

end OAI
