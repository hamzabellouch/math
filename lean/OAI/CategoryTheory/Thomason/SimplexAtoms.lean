import Mathlib
import OAI.CategoryTheory.Thomason.Linearization

namespace OAI

/-! Simplex Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Functor

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} {E : OmegaCategory.{w}}

def onCells (F : Functor C D) (n : ℕ) (x : C.Cells n) : D.Cells n :=
  ⟨F.map x.val, by rw [← F.map_source, x.property]⟩

@[simp] lemma onCells_source (F : Functor C D) (n : ℕ) (x : C.Cell) :
    F.onCells n (C.sourceCell n x) = D.sourceCell n (F.map x) :=
  Subtype.ext (F.map_source n x)

@[simp] lemma onCells_target (F : Functor C D) (n : ℕ) (x : C.Cell) :
    F.onCells n (C.targetCell n x) = D.targetCell n (F.map x) :=
  Subtype.ext (F.map_target n x)

lemma onCells_comp (F : Functor C D) {k n : ℕ} (hkn : k < n)
    (x y : C.Cells n) (h : C.target k x.val = C.source k y.val) :
    F.onCells n (C.gradedComp hkn x y h) =
      D.gradedComp hkn (F.onCells n x) (F.onCells n y) (F.map_composable h) :=
  Subtype.ext (F.map_comp k x.val y.val h _)

def lambdaRawMap (F : Functor C D) (n : ℕ) : C.LambdaRaw n →ₗ[ℤ] D.LambdaChain n :=
  Finsupp.linearCombination ℤ (fun x => D.lambdaGen (F.onCells n x))

@[simp] lemma lambdaRawMap_single (F : Functor C D) (n : ℕ) (x : C.Cells n) :
    F.lambdaRawMap n (Finsupp.single x 1) = D.lambdaGen (F.onCells n x) :=
  (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaRawMap_relations (F : Functor C D) (n : ℕ) :
    C.lambdaRelations n ≤ LinearMap.ker (F.lambdaRawMap n) := by
  apply Submodule.span_le.mpr
  intro z hz
  change F.lambdaRawMap n z = 0
  rcases hz with ⟨x, k, hk, hx, rfl⟩ | ⟨k, hk, x, y, h, rfl⟩
  · rw [F.lambdaRawMap_single]
    apply D.lambdaGen_degenerate hk
    change D.source k (F.map x.val) = F.map x.val
    rw [← F.map_source, hx]
  · simp only [map_sub, F.lambdaRawMap_single]
    rw [F.onCells_comp]
    erw [D.lambdaGen_comp hk]
    abel

def lambdaMap (F : Functor C D) (n : ℕ) : C.LambdaChain n →ₗ[ℤ] D.LambdaChain n :=
  (C.lambdaRelations n).liftQ (F.lambdaRawMap n) (F.lambdaRawMap_relations n)

@[simp] lemma lambdaMap_gen (F : Functor C D) (n : ℕ) (x : C.Cells n) :
    F.lambdaMap n (C.lambdaGen x) = D.lambdaGen (F.onCells n x) :=
  F.lambdaRawMap_single n x

lemma lambdaMap_d (F : Functor C D) (n : ℕ) :
    (F.lambdaMap n).comp (C.lambdaD n) = (D.lambdaD n).comp (F.lambdaMap (n+1)) := by
  apply C.lambda_linear_ext
  intro x
  change F.lambdaMap n (C.lambdaD n (C.lambdaGen x)) =
    D.lambdaD n (F.lambdaMap (n+1) (C.lambdaGen x))
  calc
    _ = F.lambdaMap n (C.lambdaGen (C.targetCell n x.val) -
        C.lambdaGen (C.sourceCell n x.val)) := congrArg (F.lambdaMap n) (C.lambdaD_gen n x)
    _ = F.lambdaMap n (C.lambdaGen (C.targetCell n x.val)) -
        F.lambdaMap n (C.lambdaGen (C.sourceCell n x.val)) := map_sub _ _ _
    _ = D.lambdaGen (F.onCells n (C.targetCell n x.val)) -
        D.lambdaGen (F.onCells n (C.sourceCell n x.val)) :=
      congrArg₂ (· - ·) (F.lambdaMap_gen n _) (F.lambdaMap_gen n _)
    _ = D.lambdaGen (D.targetCell n (F.map x.val)) -
        D.lambdaGen (D.sourceCell n (F.map x.val)) :=
      congrArg₂ (fun a b => D.lambdaGen a - D.lambdaGen b)
        (F.onCells_target n x.val) (F.onCells_source n x.val)
    _ = D.lambdaD n (D.lambdaGen (F.onCells (n+1) x)) :=
      (D.lambdaD_gen n (F.onCells (n+1) x)).symm
    _ = _ := congrArg (D.lambdaD n) (F.lambdaMap_gen (n+1) x).symm

lemma lambdaMap_aug (F : Functor C D) : D.lambdaAug.comp (F.lambdaMap 0) = C.lambdaAug := by
  apply C.lambda_linear_ext
  intro x
  change D.lambdaAug (F.lambdaMap 0 (C.lambdaGen x)) = C.lambdaAug (C.lambdaGen x)
  exact (congrArg D.lambdaAug (F.lambdaMap_gen 0 x)).trans
    ((D.lambdaAug_gen (F.onCells 0 x)).trans (C.lambdaAug_gen x).symm)

lemma lambdaMap_positive (F : Functor C D) (n : ℕ) (x : C.LambdaChain n)
    (hx : x ∈ C.lambdaPositive n) : F.lambdaMap n x ∈ D.lambdaPositive n := by
  change x ∈ (D.lambdaPositive n).comap (F.lambdaMap n).toAddMonoidHom
  apply AddSubmonoid.closure_le.mpr ?_ hx
  rintro z ⟨y, rfl⟩
  change F.lambdaMap n (C.lambdaGen y) ∈ D.lambdaPositive n
  rw [F.lambdaMap_gen]
  exact D.lambdaGen_positive _

def linearization (F : Functor C D) : DirectedComplex.Hom C.linearization D.linearization where
  map n := (F.lambdaMap n).toAddMonoidHom
  map_d n x := LinearMap.congr_fun (F.lambdaMap_d n) x
  map_augmentation x := LinearMap.congr_fun F.lambdaMap_aug x
  map_positive := F.lambdaMap_positive

lemma lambdaMap_id (C : OmegaCategory.{u}) (n : ℕ) :
    (Functor.id C).lambdaMap n = LinearMap.id := by
  apply C.lambda_linear_ext
  intro x
  erw [lambdaMap_gen]
  rfl

lemma lambdaMap_comp (F : Functor C D) (G : Functor D E) (n : ℕ) :
    (F.comp G).lambdaMap n = (G.lambdaMap n).comp (F.lambdaMap n) := by
  apply C.lambda_linear_ext
  intro x
  simp only [LinearMap.comp_apply]
  erw [lambdaMap_gen, lambdaMap_gen, lambdaMap_gen]
  rfl

end Thomason.OmegaCategory.Functor

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def linearizationFunctor : CategoryTheory.Functor OmegaCategory.{u} DirectedComplex.{u} where
  obj := linearization
  map := Functor.linearization
  map_id C := by
    change Functor.linearization (Functor.id C) = DirectedComplex.Hom.id C.linearization
    apply DirectedComplex.Hom.ext
    funext n
    apply AddMonoidHom.ext
    intro x
    exact LinearMap.congr_fun (Functor.lambdaMap_id C n) x
  map_comp F G := by
    change Functor.linearization (Functor.comp F G) =
      DirectedComplex.Hom.comp F.linearization G.linearization
    apply DirectedComplex.Hom.ext
    funext n
    apply AddMonoidHom.ext
    intro x
    exact LinearMap.congr_fun (F.lambdaMap_comp G n) x

lemma lambda_add_ext (C : OmegaCategory.{u}) {n : ℕ} {M : Type v} [AddCommGroup M]
    (f g : C.LambdaChain n →+ M)
    (h : ∀ x : C.Cells n, f (C.lambdaGen x) = g (C.lambdaGen x)) : f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  exact C.lambda_linear_ext f.toIntLinearMap g.toIntLinearMap h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

namespace Table

@[simp] lemma truncate_top_row {K : DirectedComplex.{u}} (k : ℕ) (e : Bool) (x : Table K) (b : Bool) :
    (truncate k e x).row k b = x.row k e := by
  simp only [truncate_row, lt_self_iff_false, ite_false, ite_true]

lemma row_above_fixed {K : DirectedComplex.{u}} (x : Table K) {k p : ℕ}
    (h : truncate k false x = x) (hkp : k < p) (b : Bool) : x.row p b = 0 := by
  have he := congrArg (fun t : Table K => t.row p b) h
  simpa only [truncate_row, show ¬p < k by omega, show p ≠ k by omega, ite_false] using he.symm

lemma row_top_fixed {K : DirectedComplex.{u}} (x : Table K) {k : ℕ}
    (h : truncate k false x = x) : x.row k false = x.row k true := by
  have he := congrArg (fun t : Table K => t.row k true) h
  simpa only [truncate_row, lt_self_iff_false, ite_false, ite_true] using he

end Table

open OmegaCategory

def lambdaCounitRaw (K : DirectedComplex.{u}) (n : ℕ) : K.nu.LambdaRaw n →ₗ[ℤ] K.Chain n :=
  Finsupp.linearCombination ℤ (fun x => x.val.row n false)

@[simp] lemma lambdaCounitRaw_single (K : DirectedComplex.{u}) (n : ℕ) (x : K.nu.Cells n) :
    K.lambdaCounitRaw n (Finsupp.single x 1) = x.val.row n false :=
  (Finsupp.linearCombination_single _ _ _).trans (one_smul ℤ _)

lemma lambdaCounitRaw_relations (K : DirectedComplex.{u}) (n : ℕ) :
    K.nu.lambdaRelations n ≤ LinearMap.ker (K.lambdaCounitRaw n) := by
  apply Submodule.span_le.mpr
  intro z hz
  change K.lambdaCounitRaw n z = 0
  rcases hz with ⟨x, k, hk, hx, rfl⟩ | ⟨k, hk, x, y, h, rfl⟩
  · rw [K.lambdaCounitRaw_single]
    exact x.val.row_above_fixed hx hk false
  · simp only [map_sub, K.lambdaCounitRaw_single]
    change (Table.comp k x.val y.val h).row n false - x.val.row n false - y.val.row n false = 0
    erw [Table.comp_row, ite_eq_right (by omega : ¬n < k), ite_eq_right (by omega : n ≠ k)]
    abel

def lambdaCounitMap (K : DirectedComplex.{u}) (n : ℕ) : K.nu.LambdaChain n →ₗ[ℤ] K.Chain n :=
  (K.nu.lambdaRelations n).liftQ (K.lambdaCounitRaw n) (K.lambdaCounitRaw_relations n)

@[simp] lemma lambdaCounitMap_gen (K : DirectedComplex.{u}) (n : ℕ) (x : K.nu.Cells n) :
    K.lambdaCounitMap n (K.nu.lambdaGen x) = x.val.row n false :=
  K.lambdaCounitRaw_single n x

lemma lambdaCounitMap_d (K : DirectedComplex.{u}) (n : ℕ) :
    (K.lambdaCounitMap n).toAddMonoidHom.comp (K.nu.lambdaD n).toAddMonoidHom =
      (K.d n).comp (K.lambdaCounitMap (n+1)).toAddMonoidHom := by
  apply K.nu.lambda_add_ext
  intro x
  change K.lambdaCounitMap n (K.nu.lambdaD n (K.nu.lambdaGen x)) =
    K.d n (K.lambdaCounitMap (n+1) (K.nu.lambdaGen x))
  erw [lambdaD_gen, map_sub, lambdaCounitMap_gen, lambdaCounitMap_gen, lambdaCounitMap_gen]
  change (Table.truncate n true x.val).row n false -
    (Table.truncate n false x.val).row n false = K.d n (x.val.row (n+1) false)
  erw [Table.truncate_row n true x.val n false, Table.truncate_row n false x.val n false]
  simp only [lt_self_iff_false, ite_false, ite_true]
  exact (x.val.boundary n false).symm

lemma lambdaCounitMap_aug (K : DirectedComplex.{u}) :
    K.augmentation.comp (K.lambdaCounitMap 0).toAddMonoidHom = K.nu.lambdaAug.toAddMonoidHom := by
  apply K.nu.lambda_add_ext
  intro x
  change K.augmentation (K.lambdaCounitMap 0 (K.nu.lambdaGen x)) = K.nu.lambdaAug (K.nu.lambdaGen x)
  erw [lambdaCounitMap_gen, lambdaAug_gen]
  exact x.val.augmentation false

lemma lambdaCounitMap_positive (K : DirectedComplex.{u}) (n : ℕ) (x : K.nu.LambdaChain n)
    (hx : x ∈ K.nu.lambdaPositive n) : K.lambdaCounitMap n x ∈ K.positive n := by
  change x ∈ (K.positive n).comap (K.lambdaCounitMap n).toAddMonoidHom
  apply AddSubmonoid.closure_le.mpr ?_ hx
  rintro z ⟨y, rfl⟩
  change K.lambdaCounitMap n (K.nu.lambdaGen y) ∈ K.positive n
  rw [K.lambdaCounitMap_gen]
  exact y.val.positive n false

def lambdaCounit (K : DirectedComplex.{u}) : Hom K.nu.linearization K where
  map n := (K.lambdaCounitMap n).toAddMonoidHom
  map_d n x := DFunLike.congr_fun (K.lambdaCounitMap_d n) x
  map_augmentation x := DFunLike.congr_fun K.lambdaCounitMap_aug x
  map_positive := K.lambdaCounitMap_positive

end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason

def lambdaNuForward {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (f : DirectedComplex.Hom C.linearization K) : OmegaCategory.Functor C K.nu :=
  C.lambdaUnit.comp f.nu

def lambdaNuBackward {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor C K.nu) : DirectedComplex.Hom C.linearization K :=
  F.linearization.comp K.lambdaCounit

lemma lambdaNuBackward_gen {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor C K.nu) (n : ℕ) (x : C.Cells n) :
    (lambdaNuBackward F).map n (C.lambdaGen x) = (F.map x.val).row n false := by
  exact (congrArg (K.lambdaCounitMap n) (F.lambdaMap_gen n x)).trans
    (K.lambdaCounitMap_gen n (F.onCells n x))

lemma lambdaNu_left_inv {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (f : DirectedComplex.Hom C.linearization K) :
    lambdaNuBackward (lambdaNuForward f) = f := by
  apply DirectedComplex.Hom.ext
  funext n
  apply C.lambda_add_ext
  intro x
  calc
    _ = ((lambdaNuForward f).map x.val).row n false :=
      lambdaNuBackward_gen (lambdaNuForward f) n x
    _ = f.map n (C.lambdaGen (C.sourceCell n x.val)) := rfl
    _ = f.map n (C.lambdaGen x) :=
      congrArg (fun z => f.map n (C.lambdaGen z)) (Subtype.ext x.property)

lemma lambdaNu_right_inv {C : OmegaCategory.{u}} {K : DirectedComplex.{v}}
    (F : OmegaCategory.Functor C K.nu) :
    lambdaNuForward (lambdaNuBackward F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  apply DirectedComplex.Table.ext
  funext p b
  cases b
  · change (lambdaNuBackward F).map p (C.lambdaGen (C.sourceCell p x)) = (F.map x).row p false
    calc
      _ = (F.map (C.source p x)).row p false := lambdaNuBackward_gen F p (C.sourceCell p x)
      _ = (DirectedComplex.Table.truncate p false (F.map x)).row p false :=
        congrArg (fun t : DirectedComplex.Table K => t.row p false) (F.map_source p x)
      _ = _ := DirectedComplex.Table.truncate_top_row p false (F.map x) false
  · change (lambdaNuBackward F).map p (C.lambdaGen (C.targetCell p x)) = (F.map x).row p true
    calc
      _ = (F.map (C.target p x)).row p false := lambdaNuBackward_gen F p (C.targetCell p x)
      _ = (DirectedComplex.Table.truncate p true (F.map x)).row p false :=
        congrArg (fun t : DirectedComplex.Table K => t.row p false) (F.map_target p x)
      _ = _ := DirectedComplex.Table.truncate_top_row p true (F.map x) false

def lambdaNuHomEquiv (C : OmegaCategory.{u}) (K : DirectedComplex.{v}) :
    DirectedComplex.Hom C.linearization K ≃ OmegaCategory.Functor C K.nu where
  toFun := lambdaNuForward
  invFun := lambdaNuBackward
  left_inv := lambdaNu_left_inv
  right_inv := lambdaNu_right_inv

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory

lemma lambdaNu_backward_natural {C D : OmegaCategory.{u}} {K : DirectedComplex.{u}}
    (F : OmegaCategory.Functor C D) (G : OmegaCategory.Functor D K.nu) :
    lambdaNuBackward (F.comp G) = F.linearization.comp (lambdaNuBackward G) := by
  apply DirectedComplex.Hom.ext
  funext n
  apply C.lambda_add_ext
  intro x
  calc
    _ = (G.map (F.map x.val)).row n false := lambdaNuBackward_gen (F.comp G) n x
    _ = (lambdaNuBackward G).map n (D.lambdaGen (F.onCells n x)) :=
      (lambdaNuBackward_gen G n (F.onCells n x)).symm
    _ = (lambdaNuBackward G).map n (F.lambdaMap n (C.lambdaGen x)) :=
      congrArg ((lambdaNuBackward G).map n) (F.lambdaMap_gen n x).symm

lemma lambdaNu_forward_natural {C : OmegaCategory.{u}} {K L : DirectedComplex.{u}}
    (f : DirectedComplex.Hom C.linearization K) (g : DirectedComplex.Hom K L) :
    lambdaNuForward (f.comp g) = (lambdaNuForward f).comp g.nu := by
  apply OmegaCategory.Functor.ext
  funext x
  apply DirectedComplex.Table.ext
  funext p b
  rfl

def lambdaNuAdjunction : OmegaCategory.linearizationFunctor.{u} ⊣ DirectedComplex.nuFunctor.{u} :=
  Adjunction.mkOfHomEquiv {
    homEquiv := lambdaNuHomEquiv
    homEquiv_naturality_left_symm := lambdaNu_backward_natural
    homEquiv_naturality_right := lambdaNu_forward_natural }

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma boundary_prepend_supported (a : E) {c : Chains E}
    (hc : c ∈ supportedOn (Set.Ici a)) :
    boundary (prepend a c) = c - prepend a (boundary c) := by
  let F : Chains E →ₗ[ℤ] Chains E :=
    boundary.comp (prepend a) - (LinearMap.id - (prepend a).comp boundary)
  have hF : supportedOn (Set.Ici a) ≤ LinearMap.ker F := by
    rw [supportedOn, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change boundary (prepend a (Finsupp.single w 1)) -
      (Finsupp.single w 1 - prepend a (boundary (Finsupp.single w 1))) = 0
    rw [← bracket_of_pairwise w.property, prepend_bracket,
      boundary_bracket (List.pairwise_cons.mpr ⟨hw, w.property.imp le_of_lt⟩),
      wordBoundary_cons, boundary_bracket (w.property.imp le_of_lt), sub_self]
  exact sub_eq_zero.mp (hF hc)

lemma prepend_positive (a : E) {c : Chains E} (hc : Positive c) : Positive (prepend a c) :=
  linearCombination_positive (fun w => bracket (a :: w.val)) (fun _ => bracket_positive _) hc

lemma prepend_mem_supportedOn {S : Set E} {a : E} (ha : a ∈ S)
    {c : Chains E} (hc : c ∈ supportedOn S) : prepend a c ∈ supportedOn S := by
  classical
  rw [prepend, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  apply bracket_mem_supportedOn
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact (mem_supportedOn_iff S c).mp hc w (Finsupp.mem_support_iff.mp hw) b hb

lemma grade_zero_eq_empty {c : Chains E} (hc : c ∈ grade 0) :
    c = emptyCoefficient c • bracket [] := by
  classical
  rw [bracket_of_pairwise List.Pairwise.nil]
  ext w
  by_cases hw : w = emptyWord
  · subst w
    simp [emptyCoefficient, emptyWord]
  · have he : c w = 0 := by
      by_contra hn
      have hlen := (mem_grade_iff 0 c).mp hc w hn
      exact hw (Subtype.ext (List.length_eq_zero_iff.mp hlen))
    have hne : w ≠ (⟨[], List.Pairwise.nil⟩ : Word E) := hw
    simp [he, Finsupp.single_eq_of_ne hne]

lemma boundary_prepend_zero (a : E) (c : (complex E).Chain 0)
    (hc : c.val ∈ supportedOn (Set.Ici a)) :
    boundary (prepend a c.val) = c.val - (complex E).augmentation c • bracket [a] := by
  rw [boundary_prepend_supported a hc,
    grade_zero_eq_empty (boundary_mem_grade c.property), map_smul, prepend_bracket]
  rfl

def coneTable (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) : Table (complex E) where
  row p b := match p with
    | 0 => if b then x.row 0 true else ⟨bracket [a], bracket_mem_grade [a]⟩
    | p+1 => if b then x.row (p+1) true +
        ⟨prepend a (x.row p false).val, prepend_mem_grade a (x.row p false).property⟩
      else ⟨prepend a (x.row p true).val, prepend_mem_grade a (x.row p true).property⟩
  positive p b := by
    cases p with
    | zero =>
      cases b
      · change Positive (bracket [a])
        exact bracket_positive [a]
      · exact x.positive 0 true
    | succ p =>
      cases b
      · exact prepend_positive a (x.positive p true)
      · exact (complex E).positive (p+1) |>.add_mem (x.positive (p+1) true)
          (prepend_positive a (x.positive p false))
  boundary p b := by
    apply Subtype.ext
    cases p with
    | zero =>
      have h0 (e : Bool) := boundary_prepend_zero a (x.row 0 e) (hx 0 e)
      simp only [x.augmentation, one_smul] at h0
      cases b
      · exact h0 true
      · change boundary ((x.row 1 true).val + prepend a (x.row 0 false).val) =
          (x.row 0 true).val - bracket [a]
        rw [map_add, h0]
        have he := congrArg Subtype.val (x.boundary 0 true)
        change boundary (x.row 1 true).val = (x.row 0 true).val - (x.row 0 false).val at he
        rw [he]
        abel
    | succ p =>
      have he (e : Bool) := congrArg Subtype.val (x.boundary p e)
      change ∀ e, boundary (x.row (p+1) e).val = (x.row p true).val - (x.row p false).val at he
      cases b
      · change boundary (prepend a (x.row (p+1) true).val) =
          ((x.row (p+1) true).val + prepend a (x.row p false).val) -
            prepend a (x.row p true).val
        rw [boundary_prepend_supported a (hx (p+1) true), he, map_sub]
        abel
      · change boundary ((x.row (p+2) true).val + prepend a (x.row (p+1) false).val) =
          ((x.row (p+1) true).val + prepend a (x.row p false).val) -
            prepend a (x.row p true).val
        rw [map_add, boundary_prepend_supported a (hx (p+1) false), he, map_sub]
        have he' := congrArg Subtype.val (x.boundary (p+1) true)
        change boundary (x.row (p+2) true).val =
          (x.row (p+1) true).val - (x.row (p+1) false).val at he'
        rw [he']
        abel
  augmentation b := by
    cases b
    · exact (vertexTable a).augmentation false
    · exact x.augmentation true
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k+1, ?_⟩
    intro p hp b
    cases p with
    | zero => omega
    | succ p =>
      have hkp : k < p := by omega
      cases b <;> apply Subtype.ext
      · change prepend a (x.row p true).val = 0
        rw [hk p hkp true]; exact map_zero _
      · change (x.row (p+1) true).val + prepend a (x.row p false).val = 0
        rw [hk (p+1) (by omega) true, hk p hkp false]
        exact (zero_add _).trans (map_zero _)

lemma coneTable_row_zero (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) (b : Bool) :
    (coneTable a x hx).row 0 b =
      if b then x.row 0 true else ⟨bracket [a], bracket_mem_grade [a]⟩ := rfl

lemma coneTable_row_succ (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) (p : ℕ) (b : Bool) :
    (coneTable a x hx).row (p+1) b =
      if b then x.row (p+1) true +
        ⟨prepend a (x.row p false).val, prepend_mem_grade a (x.row p false).property⟩
      else ⟨prepend a (x.row p true).val, prepend_mem_grade a (x.row p true).property⟩ := rfl

lemma coneTable_supported {S : Set E} {a : E} (ha : a ∈ S) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a))
    (hS : ∀ p b, (x.row p b).val ∈ supportedOn S) :
    ∀ p b, ((coneTable a x hx).row p b).val ∈ supportedOn S := by
  intro p b
  cases p with
  | zero =>
    cases b
    · exact bracket_mem_supportedOn (by simpa using ha)
    · exact hS 0 true
  | succ p =>
    cases b
    · exact prepend_mem_supportedOn ha (hS p true)
    · exact (supportedOn S).add_mem (hS (p+1) true) (prepend_mem_supportedOn ha (hS p false))

lemma coneTable_dimension (a : E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici a)) {k : ℕ}
    (hk : Table.truncate k false x = x) :
    Table.truncate (k+1) false (coneTable a x hx) = coneTable a x hx := by
  ext p b
  by_cases hp : p < k+1
  · simp only [Table.truncate_row, hp, ite_true]
  · by_cases he : p = k+1
    · subst p
      rw [Table.truncate_top_row]
      cases b
      · rfl
      · apply Subtype.ext
        change prepend a (x.row k true).val =
          (x.row (k+1) true).val + prepend a (x.row k false).val
        rw [Table.row_above_fixed x hk (by omega : k < k+1) true,
          Table.row_top_fixed x hk]
        exact (zero_add _).symm
    · rw [Table.truncate_row, ite_eq_right hp, ite_eq_right he]
      cases p with
      | zero => omega
      | succ p =>
        have hkp : k < p := by omega
        cases b <;> apply Subtype.ext
        · change 0 = prepend a (x.row p true).val
          rw [Table.row_above_fixed x hk hkp true]
          exact (map_zero _).symm
        · change 0 = (x.row (p+1) true).val + prepend a (x.row p false).val
          rw [Table.row_above_fixed x hk (by omega : k < p+1) true,
            Table.row_above_fixed x hk hkp false]
          exact ((zero_add _).trans (map_zero _)).symm

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma supportedOn_mono {S T : Set E} (h : S ⊆ T) : supportedOn S ≤ supportedOn T := by
  intro c hc
  exact (mem_supportedOn_iff T c).mpr (fun w hw a ha =>
    h ((mem_supportedOn_iff S c).mp hc w hw a ha))

structure SimplexAtomData (l : List E) where
  table : Table (complex E)
  supported : ∀ p b, (table.row p b).val ∈ supportedOn {a | a ∈ l}
  dimension : Table.truncate (l.length-1) false table = table
  top : ∀ b, (table.row (l.length-1) b).val = bracket l

namespace SimplexAtomData

def singleton (a : E) : SimplexAtomData [a] where
  table := vertexTable a
  supported p b := by
    cases p with
    | zero => exact bracket_mem_supportedOn (by simp)
    | succ p => exact (supportedOn _).zero_mem
  dimension := vertexTable_source a
  top _ := rfl

def cone (a : E) {l : List E} (hl : l ≠ []) (ha : ∀ b ∈ l, a ≤ b)
    (x : SimplexAtomData l) : SimplexAtomData (a :: l) := by
  have hx : ∀ p b, (x.table.row p b).val ∈ supportedOn (Set.Ici a) :=
    fun p b => supportedOn_mono ha (x.supported p b)
  have hlen : l.length - 1 + 1 = l.length := by
    have := List.length_pos_iff.mpr hl
    omega
  refine {
    table := coneTable a x.table hx
    supported := coneTable_supported (S := {b | b ∈ a :: l}) (by simp) x.table hx
      (fun p b => supportedOn_mono (fun _ h => List.mem_cons_of_mem a h) (x.supported p b))
    dimension := ?_
    top := ?_ }
  · simpa only [List.length_cons, Nat.add_sub_cancel, hlen] using
      coneTable_dimension a x.table hx x.dimension
  · intro b
    change ((coneTable a x.table hx).row l.length b).val = bracket (a :: l)
    rw [← hlen, coneTable_row_succ]
    have hz := Table.row_above_fixed x.table x.dimension
      (show l.length-1 < l.length-1+1 by omega) true
    cases b
    · change prepend a (x.table.row (l.length-1) true).val = bracket (a :: l)
      rw [x.top, prepend_bracket]
    · change (x.table.row (l.length-1+1) true).val +
        prepend a (x.table.row (l.length-1) false).val = bracket (a :: l)
      rw [hz, x.top, prepend_bracket]
      exact zero_add _

end SimplexAtomData

def simplexAtom : (a : E) → (l : List E) → (a :: l).Pairwise (· ≤ ·) →
    SimplexAtomData (a :: l)
  | a, [], _ => SimplexAtomData.singleton a
  | a, b :: l, h => SimplexAtomData.cone a (by simp)
      (List.pairwise_cons.mp h).1 (simplexAtom b l h.tail)

lemma basis_has_atom (w : Word E) (p : ℕ) (hw : w.val.length = p+1) :
    ∃ x : (complex E).nu.Cells p, (x.val.row p false).val = bracket w.val := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp at hw
  | cons a l =>
    let x := simplexAtom a l (hl.imp le_of_lt)
    change (a :: l).length = p+1 at hw
    have hlen : (a :: l).length-1 = p := by omega
    refine ⟨⟨x.table, ?_⟩, ?_⟩
    · change Table.truncate p false x.table = x.table
      rw [← hlen]
      exact x.dimension
    · change (x.table.row p false).val = bracket (a :: l)
      rw [← hlen]
      exact x.top false

lemma normalized_lambdaCounit_surjective (p : ℕ) :
    Function.Surjective ((complex E).lambdaCounitMap p) := by
  classical
  intro c
  have hc : c.val ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1} := c.property
  rw [Finsupp.supported_eq_span_single] at hc
  have hgen : ∀ (z : Chains E), z ∈ Submodule.span ℤ
      ((fun w : Word E => Finsupp.single w 1) '' {w | w.val.length = p+1}) →
      ∀ hz : z ∈ grade (p+1),
        (⟨z, hz⟩ : (complex E).Chain p) ∈ LinearMap.range ((complex E).lambdaCounitMap p) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rintro hg
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨x, hx⟩ := basis_has_atom w p hw
      refine ⟨(complex E).nu.lambdaGen x, ?_⟩
      rw [(complex E).lambdaCounitMap_gen]
      apply Subtype.ext
      exact hx.trans (bracket_of_pairwise w.property)
    | zero =>
      intro hg
      exact ⟨0, map_zero _⟩
    | add z y hz hy ihz ihy =>
      intro hg
      have hzg : z ∈ grade (p+1) := by
        change z ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1}
        rwa [Finsupp.supported_eq_span_single]
      have hyg : y ∈ grade (p+1) := by
        change y ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1}
        rwa [Finsupp.supported_eq_span_single]
      obtain ⟨v, hv⟩ := ihz hzg
      obtain ⟨w, hw⟩ := ihy hyg
      refine ⟨v+w, ?_⟩
      rw [map_add, hv, hw]
      rfl
    | smul r z hz ih =>
      intro hg
      have hzg : z ∈ grade (p+1) := by
        change z ∈ Finsupp.supported ℤ ℤ {w : Word E | w.val.length = p+1}
        rwa [Finsupp.supported_eq_span_single]
      obtain ⟨v, hv⟩ := ih hzg
      refine ⟨r • v, ?_⟩
      rw [map_smul, hv]
      rfl
  exact hgen c.val hc c.property

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [LinearOrder E]

lemma positive_cycle_zero {p : ℕ} {c : Chains E} (hc : c ∈ grade (p+2))
    (hp : Positive c) (hd : boundary c = 0) : c = 0 := by
  have hs : c ∈ supportedOn (∅ : Set E) :=
    positive_supportedOn_of_boundary (by intro a b hab ha; exact False.elim ha) hc hp
      (by rw [hd]; exact (supportedOn ∅).zero_mem)
  ext w
  change c w = 0
  by_contra hw
  have he := (mem_supportedOn_iff ∅ c).mp hs w hw
  have hlen := (mem_grade_iff (p+2) c).mp hc w hw
  have hn : w.val ≠ [] := by intro h; simp [h] at hlen
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hn
  exact he a ha

lemma table_endomorphism_identity (x : Table (complex E))
    (hx : x.row 0 false = x.row 0 true) : Table.truncate 0 false x = x := by
  have he : ∀ p, x.row p false = x.row p true := by
    intro p
    induction p with
    | zero => exact hx
    | succ p ih =>
      have hz (b : Bool) : x.row (p+1) b = 0 := by
        apply Subtype.ext
        apply positive_cycle_zero (x.row (p+1) b).property (x.positive (p+1) b)
        have hb := congrArg Subtype.val (x.boundary p b)
        change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
        rw [ih, sub_self] at hb
        exact hb
      rw [hz false, hz true]
  ext p b
  cases p with
  | zero =>
    rw [Table.truncate_top_row]
    cases b
    · rfl
    · exact hx
  | succ p =>
    rw [Table.truncate_row, ite_eq_right (by omega), ite_eq_right (by omega)]
    symm
    apply Subtype.ext
    apply positive_cycle_zero (x.row (p+1) b).property (x.positive (p+1) b)
    have hb := congrArg Subtype.val (x.boundary p b)
    change boundary (x.row (p+1) b).val = (x.row p true).val - (x.row p false).val at hb
    rw [he p, sub_self] at hb
    exact hb

lemma table_source_le_target (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t]) : s ≤ t := by
  classical
  by_contra hn
  have hts : t < s := lt_of_not_ge hn
  have hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici t) := by
    apply table_supportedOn_upper (by intro a b hab ha; exact le_trans ha hab) x
    intro b
    cases b
    · rw [hs]
      exact bracket_mem_supportedOn (by simpa using le_of_lt hts)
    · rw [ht]
      exact bracket_mem_supportedOn (by simp)
  let y := coneTable t x hx
  have hy0 : y.row 0 false = y.row 0 true := by
    apply Subtype.ext
    exact ht.symm
  have hy := table_endomorphism_identity y hy0
  have hy1 := congrArg Subtype.val (Table.row_above_fixed y hy (by omega : 0 < 1) true)
  change (x.row 1 true).val + prepend t (x.row 0 false).val = 0 at hy1
  rw [hs, prepend_bracket] at hy1
  let w : Word E := ⟨[t,s], by simpa using hts⟩
  have he := congrArg (fun c : Chains E => c w) hy1
  have hb : bracket [t,s] w = 1 := by rw [bracket_of_pairwise w.property]; simp [w]
  change (x.row 1 true).val w + bracket [t,s] w = 0 at he
  rw [hb] at he
  have hp := x.positive 1 true w
  omega

lemma coneTable_one_source (x : Table (complex E)) (s t : E)
    (hs : (x.row 0 false).val = bracket [s])
    (ht : (x.row 0 true).val = bracket [t])
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici s)) :
    Table.truncate 1 false (coneTable s x hx) =
      edgeTable s t (table_source_le_target x s t hs ht) := by
  ext p b
  cases p with
  | zero =>
    cases b
    · rfl
    · apply Subtype.ext; exact ht
  | succ p =>
    cases p with
    | zero =>
      rw [Table.truncate_top_row]
      apply Subtype.ext
      change prepend s (x.row 0 true).val = bracket [s,t]
      rw [ht, prepend_bracket]
    | succ p => rfl

lemma coneTable_one_target (x : Table (complex E)) (s : E)
    (hs : (x.row 0 false).val = bracket [s])
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn (Set.Ici s)) :
    Table.truncate 1 true (coneTable s x hx) = Table.truncate 1 true x := by
  ext p b
  cases p with
  | zero =>
    cases b
    · apply Subtype.ext; exact hs.symm
    · rfl
  | succ p =>
    cases p with
    | zero =>
      rw [Table.truncate_top_row, Table.truncate_top_row]
      apply Subtype.ext
      change (x.row 1 true).val + prepend s (x.row 0 false).val = (x.row 1 true).val
      rw [hs, prepend_bracket, bracket_of_not_pairwise (by simp), add_zero]
    | succ p => rfl

end Thomason.NormalizedChains

end

end OAI
