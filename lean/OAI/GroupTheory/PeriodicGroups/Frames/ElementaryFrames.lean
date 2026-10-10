import Mathlib
import OAI.GroupTheory.PeriodicGroups.Frames.AcyclicFrameEdge
import OAI.GroupTheory.PeriodicGroups.Steinberg.DiagonalActions

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.MatrixK1
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma representation_range (n : ℕ) :
    (Elementary.representation (n := n) (R := R)).range = E := by
  apply le_antisymm
  · rintro g ⟨u,rfl⟩
    have h : (⊤ : Subgroup (Steinberg n R)) ≤ E.comap Elementary.representation := by
      rw [←Steinberg.closure_range_x]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨⟨p,a⟩,rfl⟩
      change Elementary.representation (Steinberg.x p a) ∈ E
      rw [Elementary.representation_x,←SteinbergAction.elementary_eq_e]
      exact elementary_mem _ _ _ _
    exact h (Subgroup.mem_top u)
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨i,j,h,a,rfl⟩
    exact ⟨Steinberg.x ⟨i,j,h⟩ a,(Elementary.representation_x _ _).trans
      (SteinbergAction.elementary_eq_e ⟨i,j,h⟩ a).symm⟩

variable [Algebra (ZMod 2) R]
lemma permutation_mem (p : Equiv.Perm ι) : permutation (R := R) p ∈ E := by
  induction p using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul p i j h ih =>
    rw [map_mul]
    apply E.mul_mem _ ih
    rw [←SmallPresentation.evaluate_swap i j h,←evaluate_elementary]
    exact ⟨SmallPresentation.swap i j h,
      (QuotientGroup.eq_one_iff _).mp (SmallPresentation.toK1_swap i j h),rfl⟩

variable [Fintype κ] [DecidableEq κ]

omit [Algebra (ZMod 2) R] in
lemma embed_sumInl (U : (Matrix ι ι R)ˣ) :
    embed (Function.Embedding.inl (β := κ)) U = blockInclusion U := by
  apply Units.ext
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact embed_entry _ _ _ _
    | inr j =>
      simpa [blockInclusion_val,Matrix.fromBlocks,Matrix.one_apply] using
        embed_off_column (Function.Embedding.inl (α := ι)) U (.inr j) (by simp) (.inl i)
  | inr i =>
    cases j with
    | inl j =>
      simpa [blockInclusion_val,Matrix.fromBlocks,Matrix.one_apply] using
        embed_off_row (Function.Embedding.inl (α := ι)) U (.inr i) (by simp) (.inl j)
    | inr j =>
     simpa [blockInclusion_val,Matrix.fromBlocks,Matrix.one_apply] using
      embed_off_row (Function.Embedding.inl (α := ι)) U (.inr i) (by simp) (.inr j)

omit [Algebra (ZMod 2) R] in
lemma block_mem {U : (Matrix ι ι R)ˣ} (hU : U∈E) : (blockInclusion (κ := κ) U) ∈ E := by
  rw [←embed_sumInl]
  have he : E (R := R) (ι := ι) ≤ (E (R := R) (ι := ι ⊕ κ)).comap (embed (Function.Embedding.inl (β := κ))) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,j,h,a,rfl⟩
    change embed _ (elementary i j h a) ∈ E
    rw [embed_elementary]
    exact elementary_mem _ _ _ _
  exact he hU

omit [Algebra (ZMod 2) R] in
lemma rectangle_mem (A : κ × ι → Multiplicative R) : rectangleLower A ∈ E :=
  rectangleLower_mem (fun _ _ _ => elementary_mem _ _ _ _) A

omit [Algebra (ZMod 2) R] in
lemma block_smul_right (U : (Matrix ι ι R)ˣ) (j : κ) :
    blockInclusion (κ := κ) U • (Pi.single (Sum.inr j) (1 : R) : ι ⊕ κ → R) =
      (Pi.single (Sum.inr j) 1 : ι ⊕ κ → R) := by
  ext k
  change (Matrix.mulVec (blockInclusion (κ := κ) U).val _ k) = _
  rw [Matrix.mulVec_single_one]
  cases k <;> simp [blockInclusion_val, Matrix.fromBlocks,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm]

variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)

include ε hI in
lemma block_mem_iff (hι : 5≤Fintype.card ι) (U : (Matrix ι ι R)ˣ) :
    blockInclusion (κ := κ) U ∈ E ↔ U∈E := by
  rw [←embed_sumInl]
  exact embed_mem_iff ε hI _ hι U

include ε hI in

lemma ordered_transitive (hι : 5≤Fintype.card ι)
    (v : κ → ColumnFrames.Vertex (ι := ι ⊕ κ) ε)
    (hv : LinearIndependent (ZMod 2) (ColumnFrames.rho ε ∘ v)) :
    ∃U : E (R := R) (ι := ι ⊕ κ), ∀j,
      U.val • ColumnFrames.standard ε (Sum.inr j) = v j := by
  obtain ⟨U,hU⟩ := ColumnFrames.complete ε hI (Function.Embedding.inr (α := ι)) v hv
  obtain ⟨A,hA⟩ := coset_representative ε hI (Function.Embedding.inl (β := κ)) hι U
  refine ⟨⟨U*embed (Function.Embedding.inl (β := κ)) A,hA⟩,fun j => ?_⟩
  change (U*embed (Function.Embedding.inl (β := κ)) A) • _ = _
  rw [embed_sumInl,mul_smul]
  have he : blockInclusion (κ := κ) A • ColumnFrames.standard (ι := ι ⊕ κ) ε (Sum.inr j) = ColumnFrames.standard (ι := ι ⊕ κ) ε (Sum.inr j) :=
    by
      apply Subtype.ext
      change (blockInclusion (κ := κ) A •
        (Pi.single (Sum.inr j) 1 : ι ⊕ κ → R)) = Pi.single (Sum.inr j) 1
      exact block_smul_right A j
  rw [he]
  exact hU j

end SourceBurnside.Stability.MatrixK1

namespace SourceBurnside.Stability
open Classical MatrixGenerators MatrixK1 CategoryTheory
namespace ColumnRelabel
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (e : ι ≃ κ)

omit [Algebra (ZMod 2) R] in
lemma relabel_elementary_mem {U : (Matrix ι ι R)ˣ} (hU : U∈E) : relabel e U∈E := by
  have h : E (R := R) (ι := ι) ≤ (E (R := R) (ι := κ)).comap (relabel e) := by
    apply (Subgroup.closure_le _).mpr
    rintro U ⟨i,j,hij,a,rfl⟩
    change relabel e (elementary i j hij a) ∈ E
    rw [relabel_elementary]
    exact elementary_mem _ _ _ _
  exact h hU

def elementaryEquiv : E (R := R) (ι := ι) ≃* E (R := R) (ι := κ) where
  toFun U := ⟨relabel e U.val,relabel_elementary_mem e U.property⟩
  invFun U := ⟨relabel e.symm U.val,relabel_elementary_mem e.symm U.property⟩
  left_inv U := Subtype.ext (LinearAlgebra.relabel_symm_apply e.symm U.val)
  right_inv U := Subtype.ext (LinearAlgebra.relabel_symm_apply e U.val)
  map_mul' _left _right := Subtype.ext (map_mul _ _ _)

def coordinateEquiv {F : Type} [Semiring F] : (ι → F) ≃ₗ[F] (κ → F) where
  toFun v := v ∘ e.symm
  invFun v := v ∘ e
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := rfl
  map_smul' c v := rfl

def vertexEquiv : ColumnFrames.Vertex (ι := ι) ε ≃ ColumnFrames.Vertex (ι := κ) ε where
  toFun v := ⟨v.val ∘ e.symm,by
    intro hz
    apply v.property
    ext i
    have h := congrFun hz (e i)
    simpa [ColumnFrames.residue,Function.comp_def] using h⟩
  invFun v := ⟨v.val ∘ e,by
    intro hz
    apply v.property
    ext i
    have h := congrFun hz (e.symm i)
    simpa [ColumnFrames.residue,Function.comp_def] using h⟩
  left_inv v := Subtype.ext (by funext i; simp)
  right_inv v := Subtype.ext (by funext i; simp)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma rho_vertex (v : ColumnFrames.Vertex (ι := ι) ε) :
    ColumnFrames.rho ε (vertexEquiv ε e v) = coordinateEquiv (F := ZMod 2) e (ColumnFrames.rho ε v) := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma independent (s : Set (ColumnFrames.Vertex (ι := ι) ε))
    (hs : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) s) :
    LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) (vertexEquiv ε e '' s) := by
  have h := hs.map_injOn (coordinateEquiv (F := ZMod 2) e).toLinearMap
    (fun a _ b _ hab => (coordinateEquiv (F := ZMod 2) e).injective hab)
  have hh : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε ∘ vertexEquiv ε e) s :=
    h.congr (fun v _ => (rho_vertex ε e v).symm)
  exact hh.image_of_comp (vertexEquiv ε e) (ColumnFrames.rho ε)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma independent_symm (s : Set (ColumnFrames.Vertex (ι := κ) ε))
    (hs : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) s) :
    LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) ((vertexEquiv ε e).symm '' s) :=
  independent ε e.symm s hs

lemma vertex_action (g : E (R := R) (ι := ι)) (v : ColumnFrames.Vertex (ι := ι) ε) :
    vertexEquiv ε e (g • v) = elementaryEquiv e g • vertexEquiv ε e v := by
  apply Subtype.ext
  ext j
  change (∑i, g.val.val (e.symm j) i * v.val i) =
    ∑k, g.val.val (e.symm j) (e.symm k) * v.val (e.symm k)
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

lemma independent_action (g : E (R := R) (ι := ι))
    (s : Set (ColumnFrames.Vertex (ι := ι) ε)) (hs : LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) s) :
    LinearIndepOn (ZMod 2) (ColumnFrames.rho ε) ((g • ·) '' s) := ColumnFrames.independent_map ε g.val hs

variable [LinearOrder (ColumnFrames.Vertex (ι := ι) ε)]
variable [LinearOrder (ColumnFrames.Vertex (ι := κ) ε)]

def homologyIso (k n : ℕ) :
    groupHomology (Frames.chainRep (E (R := R) (ι := ι)) (ρ := ColumnFrames.rho ε) (independent_action ε) k) n ≅
    groupHomology (Frames.chainRep (E (R := R) (ι := κ)) (ρ := ColumnFrames.rho ε) (independent_action ε) k) n :=
  Frames.chainHomologyIso (ColumnFrames.rho ε) (ColumnFrames.rho ε) (vertexEquiv ε e)
    (independent ε e) (independent_symm ε e) (independent_action ε) (independent_action ε)
    (elementaryEquiv e) (vertex_action ε e) k n

end ColumnRelabel
end SourceBurnside.Stability

end

end OAI
