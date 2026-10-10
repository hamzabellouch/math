import Mathlib
import OAI.Geometry.NilpotentCharts.Coordinates
import OAI.Geometry.NilpotentCharts.SmoothCalculus

namespace OAI

/-! Polynomial commutator words and rational central spans. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawCentralWords
inductive Word : ℕ → ℕ → Type
  | var : Word 0 1
  | unit (k : ℕ) : Word k 0
  | prod {k n m : ℕ} (a : Word k n) (b : Word k m) : Word k (n+m)
  | inv {k n : ℕ} (a : Word k n) : Word k n
  | bracket {k n m : ℕ} (a : Word k n) (b : Word 0 m) : Word (k+1) (n+m)

variable {G : Type*} [Group G]
def Word.eval : {k n : ℕ} → Word k n → (Fin n → G) → G
  | _,_,.var,a => a 0
  | _,_,.unit _,_ => 1
  | _,_,.prod w v,a => w.eval (a ∘ Fin.castAdd _) * v.eval (a ∘ Fin.natAdd _)
  | _,_,.inv w,a => (w.eval a)⁻¹
  | _,_,.bracket w v,a => ⁅w.eval (a ∘ Fin.castAdd _),v.eval (a ∘ Fin.natAdd _)⁆

lemma Word.eval_one {k n : ℕ} (w : Word k n) : w.eval (fun _ => (1 : G)) = 1 := by
  induction w with
  | var => rfl
  | unit => rfl
  | prod a b ha hb => simp only [Word.eval,Function.comp_def,ha,hb,mul_one]
  | inv a ha => simp only [Word.eval,ha,inv_one]
  | bracket a b ha hb => simp only [Word.eval,Function.comp_def,ha,hb,commutatorElement_one_left]

lemma Word.eval_mem {k n : ℕ} (w : Word k n) (a : Fin n → G) :
    w.eval a ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
  induction w with
  | var => trivial
  | unit k => exact Subgroup.one_mem _
  | prod w v hw hv => exact Subgroup.mul_mem _ (hw _) (hv _)
  | inv w hw => exact Subgroup.inv_mem _ (hw _)
  | bracket w v hw hv => exact Subgroup.commutator_mem_commutator (hw _) (hv _)

lemma Word.eval_subgroup {k n : ℕ} (w : Word k n) (a : Fin n → G)
    (S : Subgroup G) (ha : ∀ i, a i ∈ S) : w.eval a ∈ S := by
  induction w with
  | var => exact ha _
  | unit => exact S.one_mem
  | prod w v hw hv => exact S.mul_mem (hw _ (fun i => ha _)) (hv _ (fun i => ha _))
  | inv w hw => exact S.inv_mem (hw _ ha)
  | bracket w v hw hv =>
    have hx := hw (a ∘ Fin.castAdd _) (fun i => ha _)
    have hy := hv (a ∘ Fin.natAdd _) (fun i => ha _)
    exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)

def wordSubgroup (k : ℕ) : Subgroup G where
  carrier := {g | ∃ (n : ℕ) (w : Word k n) (a : Fin n → G), w.eval a = g}
  one_mem' := ⟨0,.unit k,fun i => Fin.elim0 i,rfl⟩
  mul_mem' := by
    rintro x y ⟨n,w,a,rfl⟩ ⟨m,v,b,rfl⟩
    refine ⟨n+m,.prod w v,Fin.append a b,?_⟩
    simp only [Word.eval,Function.comp_def,Fin.append_left,Fin.append_right]
  inv_mem' := by rintro x ⟨n,w,a,rfl⟩; exact ⟨n,.inv w,a,rfl⟩

lemma wordSubgroup_eq (k : ℕ) : wordSubgroup (G := G) k = (⊤ : Subgroup G).lowerCentralSeries k := by
  apply le_antisymm
  · rintro x ⟨n,w,a,rfl⟩
    exact w.eval_mem a
  · induction k with
    | zero => intro x _; exact ⟨1,.var,fun _ => x,rfl⟩
    | succ k ih =>
      apply Subgroup.commutator_le.mpr
      intro x hx y hy
      obtain ⟨n,w,a,rfl⟩ := ih hx
      refine ⟨n+1,.bracket w .var,Fin.append a (fun _ => y),?_⟩
      simp only [Word.eval,Function.comp_def,Fin.append_left,Fin.append_right]

lemma exists_word {k : ℕ} {g : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    ∃ (n : ℕ) (w : Word k n) (a : Fin n → G), w.eval a = g := by
  rw [← wordSubgroup_eq] at hg
  exact hg
end RawCentralWords

namespace RawCentralWords
open RationalLattice RawPolynomial
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
  (c : RealCoordinates G n) {σ : Type*}
lemma Word.isPoly_eval {k m : ℕ} (w : Word k m) (a : (σ → ℝ) → Fin m → G)
    (ha : ∀ i, IsPolyCoord c (fun x => a x i)) : IsPolyCoord c (fun x => w.eval (a x)) := by
  induction w with
  | var => exact ha 0
  | unit => exact IsPolyCoord.const c 1
  | prod w v hw hv =>
    exact (hw (fun x => a x ∘ Fin.castAdd _) (fun i => ha _)).mul c
      (hv (fun x => a x ∘ Fin.natAdd _) (fun i => ha _))
  | inv w hw => exact (hw a ha).inv c
  | bracket w v hw hv =>
    exact (hw (fun x => a x ∘ Fin.castAdd _) (fun i => ha _)).bracket c
      (hv (fun x => a x ∘ Fin.natAdd _) (fun i => ha _))

lemma Word.isPoly_coords_eval {k m : ℕ} (w : Word k m) :
    IsPolyCoord c (fun x : Fin m × Fin n → ℝ =>
      w.eval (fun i => c.coord.symm (fun j => x (i,j)))) := by
  apply w.isPoly_eval c
  intro i j
  simpa only [c.coord.apply_symm_apply] using (isPoly_coordinate (i,j))
end RawCentralWords

namespace RawCentralWords
open RationalLattice RawPolynomial
open scoped commutatorElement
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  {n : ℕ} (c : RealCoordinates G n) (L : (Fin n → ℝ) →ₗ[ℝ] C)

def wordLog {k m : ℕ} (w : Word k m) (x : Fin m × Fin n → ℝ) : C :=
  L (c.coord (w.eval (fun i => c.coord.symm (fun j => x (i,j)))))

omit [IsTopologicalGroup G] [FiniteDimensional ℝ C] in
lemma wordLog_poly {k m d : ℕ} (w : Word k m) (b : Module.Basis (Fin d) ℝ C) :
    IsPolyVec b (wordLog c L w) :=
  isPolyVec_linear_coordinates b L _ (w.isPoly_coords_eval c)

omit [IsTopologicalGroup G] in
lemma coord_symm_zero : c.coord.symm 0 = 1 := by
  apply c.coord.injective
  rw [c.coord.apply_symm_apply]
  exact funext (fun i => (c.one_coord i).symm)

omit [IsTopologicalGroup G] [FiniteDimensional ℝ C] in
lemma wordLog_zero {k m : ℕ} (w : Word k m) : wordLog c L w 0 = 0 := by
  unfold wordLog
  have hi : (fun i : Fin m => c.coord.symm (fun j : Fin n => (0 : Fin m × Fin n → ℝ) (i,j))) = fun _ => 1 := by
    funext i
    exact coord_symm_zero c
  rw [hi,w.eval_one,show c.coord 1 = 0 from funext c.one_coord,map_zero]

def centralWordSpan (k : ℕ) : Submodule ℝ C :=
  Submodule.span ℝ {v | ∃ (m : ℕ) (w : Word k m) (x : Fin m × Fin n → ℝ), wordLog c L w x = v}

variable (φ : Multiplicative C →* G) (S : Subgroup G) (k : ℕ)
  (hCS : (⊤ : Subgroup G).lowerCentralSeries k ≤ S)
  (hlift : ∀ g ∈ S, φ (Multiplicative.ofAdd (L (c.coord g))) = g)

omit [IsTopologicalGroup G] [FiniteDimensional ℝ C] in
include hCS hlift in
lemma wordLog_map {m : ℕ} (w : Word k m) (x : Fin m × Fin n → ℝ) :
    φ (Multiplicative.ofAdd (wordLog c L w x)) =
      w.eval (fun i => c.coord.symm (fun j => x (i,j))) :=
  hlift _ (hCS (w.eval_mem _))

def vectorSubgroup (K : Submodule ℝ C) : Subgroup G :=
  (K.toAddSubgroup.toSubgroup).map φ

omit [IsTopologicalGroup G] in
lemma vectorSubgroup_closed (K : Submodule ℝ C)
    (hφ : Topology.IsClosedEmbedding (fun v : C => φ (Multiplicative.ofAdd v))) :
    IsClosed (vectorSubgroup φ K : Set G) := by
  have he : (vectorSubgroup φ K : Set G) = (fun v : C => φ (Multiplicative.ofAdd v)) '' (K : Set C) := by
    ext g
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨v.toAdd,hv,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨Multiplicative.ofAdd v,hv,rfl⟩
  rw [he]
  exact hφ.isClosedMap _ K.closed_of_finiteDimensional

include hCS hlift in
lemma centralWordSpan_closure
    (hφ : Topology.IsClosedEmbedding (fun v : C => φ (Multiplicative.ofAdd v))) :
    vectorSubgroup φ (centralWordSpan c L k) =
      ((⊤ : Subgroup G).lowerCentralSeries k).topologicalClosure := by
  let H : AddSubgroup C := (((⊤ : Subgroup G).lowerCentralSeries k).topologicalClosure.comap φ).toAddSubgroup
  have hH : IsClosed (H : Set C) :=
    (Subgroup.isClosed_topologicalClosure _).preimage hφ.continuous
  have hword (m : ℕ) (w : Word k m) (x : Fin m × Fin n → ℝ) :
      wordLog c L w x ∈ RawClosedAddGroup.vectorPart H := by
    let f : ℝ → C := fun t => wordLog c L w (t • x)
    have hf : Differentiable ℝ f := (wordLog_poly c L w (Module.finBasis ℝ C)).comp_differentiable
      (fun _ => differentiable_id.mul_const _)
    have hm : ∀ t, f t ∈ H := by
      intro t
      change φ (Multiplicative.ofAdd (wordLog c L w (t • x))) ∈ ((⊤ : Subgroup G).lowerCentralSeries k).topologicalClosure
      rw [wordLog_map c L φ S k hCS hlift]
      exact Subgroup.le_topologicalClosure _ (w.eval_mem _)
    have h0 : f 0 = 0 := by simp only [f,zero_smul,wordLog_zero]
    simpa only [f,one_smul] using RawClosedAddGroup.curve_mem_vectorPart H hH hf hm h0 1
  have hK : centralWordSpan c L k ≤ RawClosedAddGroup.vectorPart H := by
    apply Submodule.span_le.mpr
    rintro v ⟨m,w,x,rfl⟩
    exact hword m w x
  apply le_antisymm
  · rintro g ⟨v,hv,rfl⟩
    exact RawClosedAddGroup.vectorPart_le H (hK hv)
  · apply Subgroup.topologicalClosure_minimal
    · intro g hg
      obtain ⟨m,w,a,rfl⟩ := exists_word hg
      let x : Fin m × Fin n → ℝ := fun ij => c.coord (a ij.1) ij.2
      have he : (fun i => c.coord.symm (fun j => x (i,j))) = a := by
        funext i
        exact c.coord.symm_apply_apply (a i)
      refine ⟨Multiplicative.ofAdd (wordLog c L w x),?_,?_⟩
      · change wordLog c L w x ∈ centralWordSpan c L k
        exact Submodule.subset_span ⟨m,w,x,rfl⟩
      · simpa only [he] using wordLog_map c L φ S k hCS hlift w x
    · exact vectorSubgroup_closed φ _ hφ

omit [IsTopologicalGroup G] in
include hCS hlift in
lemma centralWordSpan_lattice_span (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j = z) :
    Submodule.span ℝ {v : C | v ∈ centralWordSpan c L k ∧ φ (Multiplicative.ofAdd v) ∈ Γ} =
      centralWordSpan c L k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    exact fun _ h => h.1
  · apply Submodule.span_le.mpr
    rintro v ⟨m,w,x,rfl⟩
    apply Submodule.span_mono (s := Set.range (fun z : (Fin m × Fin n) → ℤ =>
      wordLog c L w (fun i => (z i : ℝ)))) ?_ ((wordLog_poly c L w (Module.finBasis ℝ C)).mem_span_integer_grid x)
    rintro v ⟨z,rfl⟩
    refine ⟨Submodule.subset_span ⟨m,w,_,rfl⟩,?_⟩
    rw [wordLog_map c L φ S k hCS hlift]
    apply w.eval_subgroup _ Γ
    intro i
    apply (hΓ _).mpr
    intro j
    exact ⟨z (i,j),by rw [c.coord.apply_symm_apply]⟩
end RawCentralWords
end

end OAI
