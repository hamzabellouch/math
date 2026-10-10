import OAI.GroupTheory.Congruence.Basic
import OAI.GroupTheory.Congruence.Patterns

namespace OAI

/-!
Affine and rational lattices, polynomial congruence actions, and lattice-chain geometry.
-/

noncomputable section


namespace CoboundaryExpanders.AffineLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
open scoped BigOperators

variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

def level : ℕ → P
  | 0 => C
  | m+1 => T (level m)

@[simp] lemma level_zero : level T C 0 = C := rfl
@[simp] lemma level_succ (m : ℕ) : level T C (m+1) = T (level T C m) := rfl

lemma level_antitone (hC : T C ≤ C) : Antitone (level T C) := by
  apply antitone_nat_of_succ_le
  intro m
  induction m with
  | zero => exact hC
  | succ m ih => exact T.monotone ih

lemma level_le (hC : T C ≤ C) (m : ℕ) : level T C m ≤ C :=
  level_antitone T C hC (Nat.zero_le m)

def IsVertex (A : P) : Prop :=
  A ≤ C ∧ ¬ A ≤ T C ∧ (∃ m, level T C m ≤ A) ∧ T A ≤ A

abbrev Vertex := {A : P // IsVertex T C A}

instance : PartialOrder (Vertex T C) := Subtype.partialOrder _

noncomputable instance : DecidableEq (Vertex T C) := Classical.decEq _

lemma vertex_le (A : Vertex T C) : (A : P) ≤ C := A.property.1
lemma vertex_normalized (A : Vertex T C) : ¬ (A : P) ≤ T C := A.property.2.1
lemma vertex_bounded (A : Vertex T C) : ∃ m, level T C m ≤ (A : P) := A.property.2.2.1
lemma vertex_shift_le (A : Vertex T C) : T (A : P) ≤ (A : P) := A.property.2.2.2

def base (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) : Vertex T C :=
  ⟨C,le_rfl,hstrict,⟨0,le_rfl⟩,hC⟩

def IsFace (s : Finset (Vertex T C)) : Prop :=
  (∀ A ∈ s, ∀ B ∈ s, A ≤ B ∨ B ≤ A) ∧
  (∀ A ∈ s, ∀ B ∈ s, T (A : P) ≤ (B : P))

def complex : InfiniteChains.Complex (Vertex T C) where
  faces := {s | IsFace T C s}
  empty_mem := by simp [IsFace]
  downward := by
    intro s t hs ht
    exact ⟨fun A hA B hB => hs.1 A (ht hA) B (ht hB),
      fun A hA B hB => hs.2 A (ht hA) B (ht hB)⟩

lemma singleton_face (A : Vertex T C) : IsFace T C {A} := by
  constructor
  · intro B hB D hD
    simp only [Finset.mem_singleton] at hB hD
    subst B; subst D
    exact Or.inl le_rfl
  · intro B hB D hD
    simp only [Finset.mem_singleton] at hB hD
    subst B; subst D
    exact vertex_shift_le T C A

def ball (m : ℕ) : InfiniteChains.Complex (Vertex T C) where
  faces := {s | IsFace T C s ∧ ∀ A ∈ s, level T C m ≤ (A : P)}
  empty_mem := ⟨(complex T C).empty_mem,by simp⟩
  downward := fun hs ht => ⟨(complex T C).downward hs.1 ht,fun A hA => hs.2 A (ht hA)⟩

lemma ball_mono (hC : T C ≤ C) {a b : ℕ} (hab : a ≤ b) :
    (ball T C a).faces ⊆ (ball T C b).faces := by
  intro s hs
  exact ⟨hs.1,fun A hA => (level_antitone T C hC hab).trans (hs.2 A hA)⟩

def raise (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) : Vertex T C :=
  ⟨(A : P) ⊔ level T C m, sup_le (vertex_le T C A) (level_le T C hC m),
    fun h => vertex_normalized T C A (le_sup_left.trans h),
    ⟨m,le_sup_right⟩, by
      rw [T.map_sup]
      exact sup_le_sup (vertex_shift_le T C A) (level_antitone T C hC (Nat.le_succ m))⟩

@[simp] lemma raise_val (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) :
    (raise T C hC m A : P) = (A : P) ⊔ level T C m := rfl

lemma le_raise (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) :
    A ≤ raise T C hC m A := le_sup_left

lemma raise_good (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) :
    level T C m ≤ (raise T C hC m A : P) := le_sup_right

lemma raise_ne (hC : T C ≤ C) (m : ℕ) (A : Vertex T C)
    (hA : ¬ level T C m ≤ (A : P)) : raise T C hC m A ≠ A := by
  intro he
  exact hA (he ▸ raise_good T C hC m A)

lemma insert_raise_face (hC : T C ≤ C) (m : ℕ) (A : Vertex T C)
    (s : Finset (Vertex T C)) (hs : insert A s ∈ (ball T C (m+1)).faces)
    (hmax : ∀ B ∈ s, A < B → level T C m ≤ (B : P)) :
    insert (raise T C hC m A) (insert A s) ∈ (ball T C (m+1)).faces := by
  let v := raise T C hC m A
  have hAv : A ≤ v := le_raise T C hC m A
  have hcmp : ∀ B ∈ insert A s, B ≤ v ∨ v ≤ B := by
    intro B hB
    rcases (hs.1.1 A (Finset.mem_insert_self _ _) B hB) with hAB | hBA
    · by_cases he : A = B
      · subst B; exact Or.inl hAv
      · have hBs : B ∈ s := (Finset.mem_insert.mp hB).resolve_left (Ne.symm he)
        exact Or.inr (sup_le hAB (hmax B hBs (lt_of_le_of_ne hAB he)))
    · exact Or.inl (hBA.trans hAv)
  have hTv : ∀ B ∈ insert A s, T (v : P) ≤ (B : P) := by
    intro B hB
    change T ((A : P) ⊔ level T C m) ≤ _
    rw [T.map_sup]
    exact sup_le (hs.1.2 A (Finset.mem_insert_self _ _) B hB) (hs.2 B hB)
  have hTo : ∀ B ∈ insert A s, T (B : P) ≤ (v : P) := by
    intro B hB
    exact (hs.1.2 B hB A (Finset.mem_insert_self _ _)).trans hAv
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB D hD
    rcases Finset.mem_insert.mp hB with rfl | hB
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact Or.inl le_rfl
      · exact (hcmp D hD).symm
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hcmp B hB
      · exact hs.1.1 B hB D hD
  · intro B hB D hD
    rcases Finset.mem_insert.mp hB with rfl | hB
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact vertex_shift_le T C v
      · exact hTv D hD
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hTo B hB
      · exact hs.1.2 B hB D hD
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact (level_antitone T C hC (Nat.le_succ m)).trans (raise_good T C hC m A)
    · exact hs.2 B hB

lemma eliminate_maximal (hC : T C ≤ C) (m r : ℕ)
    (A : Finset (Vertex T C)) (v : Vertex T C)
    (hv : Maximal (· ∈ A) v)
    (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (allowed (ball T C (m+1))
      (fun w => ¬ level T C m ≤ (w : P)) A).faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ e c' : Raw (Vertex T C),
      e ∈ supported (graded (ball T C (m+1)).faces (r+2)) ∧
      c' ∈ supported (graded (allowed (ball T C (m+1))
        (fun w => ¬ level T C m ≤ (w : P)) (A.erase v)).faces (r+1)) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c := by
  classical
  let X := ball T C (m+1)
  let bad := fun w : Vertex T C => ¬ level T C m ≤ (w : P)
  let v' := raise T C hC m v
  let L : Set (Finset (Vertex T C)) := {s | insert v s ∈ X.faces ∧
    v ∉ s ∧ ∀ w ∈ s, bad w → w ∈ A.erase v}
  have hlink : link v c ∈ supported (graded L r) := by
    apply link_graded v (allowed X bad A).faces L r ?_ c hc
    intro s hs hvs
    refine ⟨?_,Finset.notMem_erase _ _,?_⟩
    · simpa only [Finset.insert_erase hvs] using hs.1
    · intro w hw hbw
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1,
        hs.2 w (Finset.mem_of_mem_erase hw) hbw⟩
  let Q : Set (Finset (Vertex T C)) := {s | s ∈ (allowed X bad (A.erase v)).faces ∧
    insert v s ∈ X.faces}
  have hcone : ∀ s ∈ L, v' ∉ s → insert v' s ∈ Q := by
    intro s hs _
    have hm : ∀ w ∈ s, v < w → level T C m ≤ (w : P) := by
      intro w hw hvw
      by_contra hbw
      have hwA := Finset.mem_of_mem_erase (hs.2.2 w hw hbw)
      exact (not_le_of_gt hvw) (hv.2 hwA hvw.le)
    have hi := insert_raise_face T C hC m v s hs.1 hm
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact X.downward hi (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    · intro w hw hbw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (hbw (raise_good T C hC m v))
      · exact hs.2.2 w hw hbw
    · simpa only [Finset.insert_comm] using hi
  let b := rawCone v' (link v c)
  have hb : b ∈ supported (graded Q (r+1)) := rawCone_graded v' L Q r hcone _ hlink
  have hdb : rawBoundary b = link v c := by
    have he := LinearMap.congr_fun (raw_contraction v') (link v c)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,
      link_cycle v c hz,map_zero,add_zero] using he
  refine ⟨rawCone v b,without v c + b,?_,?_,elimination_cycle v c b hz hdb,
    elimination_identity v c b hdb⟩
  · exact rawCone_graded v Q X.faces (r+1) (fun s hs _ => hs.2) b hb
  · apply Submodule.add_mem
    · have hw := without_supported v (graded (allowed X bad A).faces (r+1)) c hc
      apply supported_mono ?_ hw
      intro s hs
      refine ⟨⟨hs.1.1.1,?_⟩,hs.1.2⟩
      intro w hw hbw
      exact Finset.mem_erase.mpr ⟨fun he => hs.2 (he ▸ hw),hs.1.1.2 w hw hbw⟩
    · apply supported_mono (P := graded Q (r+1)) ?_ hb
      intro s hs
      exact ⟨hs.1.1,hs.2⟩

lemma push_cycle_down (hC : T C ≤ C) (m r : ℕ)
    (A : Finset (Vertex T C)) (hA : ∀ v ∈ A, ¬ level T C m ≤ (v : P))
    (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (allowed (ball T C (m+1))
      (fun w => ¬ level T C m ≤ (w : P)) A).faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ e c' : Raw (Vertex T C),
      e ∈ supported (graded (ball T C (m+1)).faces (r+2)) ∧
      c' ∈ supported (graded (ball T C m).faces (r+1)) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c := by
  classical
  induction A using Finset.strongInductionOn generalizing c with
  | _ A ih =>
    by_cases hne : A.Nonempty
    · obtain ⟨v,hv⟩ := A.exists_maximal hne
      obtain ⟨e,c',he,hc',hz',hec⟩ := eliminate_maximal T C hC m r A v hv c hc hz
      obtain ⟨f,c'',hf,hc'',hz'',hfc⟩ :=
        ih (A.erase v) (Finset.erase_ssubset hv.1)
          (fun w hw => hA w (Finset.mem_of_mem_erase hw)) c' hc' hz'
      refine ⟨e+f,c'',Submodule.add_mem _ he hf,hc'',hz'',?_⟩
      rw [map_add,add_assoc,hfc,hec]
    · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst A
      refine ⟨0,c,Submodule.zero_mem _,?_,hz,by simp⟩
      apply supported_mono ?_ hc
      intro s hs
      refine ⟨⟨hs.1.1.1,?_⟩,hs.2⟩
      intro v hv
      by_contra hbad
      exact Finset.notMem_empty v (hs.1.2 v hv hbad)

lemma push_ball_cycle (hC : T C ≤ C) (m r : ℕ)
    (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (ball T C (m+1)).faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ e c' : Raw (Vertex T C),
      e ∈ supported (graded (ball T C (m+1)).faces (r+2)) ∧
      c' ∈ supported (graded (ball T C m).faces (r+1)) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c := by
  classical
  let A : Finset (Vertex T C) := (vertices c).filter (fun (v : Vertex T C) => ¬ level T C m ≤ (v : P))
  apply push_cycle_down T C hC m r A (fun v hv => (Finset.mem_filter.mp hv).2) c ?_ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1,?_⟩,(hc s hs).2⟩
  intro v hv hbad
  exact Finset.mem_filter.mpr ⟨mem_vertices c s hs v hv,hbad⟩

lemma ball_zero_face (hC : T C ≤ C) (hstrict : ¬ C ≤ T C)
    (s : Finset (Vertex T C)) (hs : s ∈ (ball T C 0).faces) :
    insert (base T C hC hstrict) s ∈ (ball T C 0).faces := by
  have he : ∀ v ∈ s, v = base T C hC hstrict := by
    intro v hv
    apply Subtype.ext
    exact le_antisymm (vertex_le T C v) (hs.2 v hv)
  have hsub : insert (base T C hC hstrict) s ⊆ {base T C hC hstrict} := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · simp [he v hv]
  refine (ball T C 0).downward ?_ hsub
  exact ⟨singleton_face T C _,by simp [base]⟩

theorem ball_exact (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (m r : ℕ) :
    ExactIn (ball T C m).faces (r+1) := by
  induction m with
  | zero =>
    intro c hc hz
    refine ⟨rawCone (base T C hC hstrict) c,
      rawCone_graded _ _ _ _ (fun s hs _ => ball_zero_face T C hC hstrict s hs) c hc,?_⟩
    have he := LinearMap.congr_fun (raw_contraction (base T C hC hstrict)) c
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,hz,map_zero,add_zero] using he
  | succ m ih =>
    intro c hc hz
    obtain ⟨e,c',he,hc',hz',hec⟩ := push_ball_cycle T C hC m r c hc hz
    obtain ⟨b,hb,hbc⟩ := ih c' hc' hz'
    refine ⟨e+b,Submodule.add_mem _ he ?_,?_⟩
    · apply supported_mono (P := graded (ball T C m).faces (r+2)) ?_ hb
      intro s hs
      exact ⟨ball_mono T C hC (Nat.le_succ m) hs.1,hs.2⟩
    · rw [map_add,hbc,hec]

lemma finite_ball (hC : T C ≤ C) (r : ℕ) (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (complex T C).faces r)) :
    ∃ m, c ∈ supported (graded (ball T C m).faces r) := by
  classical
  have hex : ∀ v ∈ vertices c, ∃ m, level T C m ≤ (v : P) := fun v _ => vertex_bounded T C v
  choose f hf using hex
  let m := (vertices c).sup (fun v => if h : v ∈ vertices c then f v h else 0)
  refine ⟨m,?_⟩
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1,?_⟩,(hc s hs).2⟩
  intro v hv
  have hvc := mem_vertices c s hs v hv
  have hfm : f v hvc ≤ m := by
    simpa only [dite_eq_left hvc] using Finset.le_sup (f := fun v => if h : v ∈ vertices c then f v h else 0) hvc
  exact (level_antitone T C hC hfm).trans (hf v hvc)

theorem complex_exact (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (r : ℕ) :
    ExactIn (complex T C).faces (r+1) := by
  intro c hc hz
  obtain ⟨m,hm⟩ := finite_ball T C hC (r+1) c hc
  obtain ⟨b,hb,hbc⟩ := ball_exact T C hC hstrict m r c hm hz
  refine ⟨b,?_,hbc⟩
  apply supported_mono (P := graded (ball T C m).faces (r+2)) ?_ hb
  intro s hs
  exact ⟨hs.1.1,hs.2⟩

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

abbrev V := Fin N → RatFunc K
abbrev LatticeSpace := Submodule K[X] (V K N)

def uniformizer : RatFunc K := algebraMap K[X] (RatFunc K) Polynomial.X
lemma uniformizer_ne_zero : uniformizer K ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

noncomputable def shiftLinear : V K N ≃ₗ[K[X]] V K N :=
  (LinearEquiv.smulOfNeZero (RatFunc K) (V K N) (uniformizer K)
    (uniformizer_ne_zero K)).restrictScalars K[X]

@[simp] lemma shiftLinear_apply (v : V K N) (i : Fin N) :
    shiftLinear K N v i = uniformizer K * v i := rfl

noncomputable def shift : LatticeSpace K N ≃o LatticeSpace K N :=
  Submodule.orderIsoMapComap (shiftLinear K N)

def standard : LatticeSpace K N where
  carrier := {v | ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f = v i}
  zero_mem' := fun _ => ⟨0,map_zero _⟩
  add_mem' := by
    intro v w hv hw i
    obtain ⟨f,hf⟩ := hv i
    obtain ⟨g,hg⟩ := hw i
    exact ⟨f+g,by simp only [map_add,hf,hg,Pi.add_apply]⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨f,hf⟩ := hv i
    refine ⟨a*f,?_⟩
    simp only [map_mul,hf,Pi.smul_apply,Algebra.smul_def]

lemma mem_standard (v : V K N) : v ∈ standard K N ↔
    ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f = v i := Iff.rfl

lemma mem_shift (A : LatticeSpace K N) (v : V K N) :
    v ∈ shift K N A ↔ ∃ w ∈ A, shiftLinear K N w = v :=
  Submodule.mem_map

lemma shift_standard_le : shift K N (standard K N) ≤ standard K N := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
  intro i
  obtain ⟨f,hf⟩ := hw i
  refine ⟨Polynomial.X*f,?_⟩
  simp only [map_mul,hf,shiftLinear_apply,uniformizer]

lemma shift_le_self (A : LatticeSpace K N) : shift K N A ≤ A := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
  have he : shiftLinear K N w = (Polynomial.X : K[X]) • w := by
    ext i
    simp only [shiftLinear_apply,Pi.smul_apply,Algebra.smul_def,uniformizer]
  rw [he]
  exact A.smul_mem Polynomial.X hw

lemma standard_not_le_shift (hN : 0 < N) :
    ¬ standard K N ≤ shift K N (standard K N) := by
  intro hle
  let v : V K N := fun _ => 1
  have hv : v ∈ standard K N := fun _ => ⟨1,map_one _⟩
  obtain ⟨w,hw,he⟩ := (mem_shift K N _ _).mp (hle hv)
  obtain ⟨f,hf⟩ := hw ⟨0,hN⟩
  have hm : algebraMap K[X] (RatFunc K) (Polynomial.X*f) =
      algebraMap K[X] (RatFunc K) 1 := by
    simpa only [map_mul,hf,map_one,uniformizer,shiftLinear_apply] using
      congr_fun he ⟨0,hN⟩
  have hp : Polynomial.X*f = 1 := RatFunc.algebraMap_injective K hm
  have hc := congrArg Polynomial.constantCoeff hp
  simp at hc

noncomputable abbrev Vertex := AffineLattices.Vertex (shift K N) (standard K N)
noncomputable abbrev building : InfiniteChains.Complex (Vertex K N) :=
  AffineLattices.complex (shift K N) (standard K N)

theorem building_exact (hN : 0 < N) (r : ℕ) :
    ExactIn (building K N).faces (r+1) :=
  AffineLattices.complex_exact (shift K N) (standard K N)
    (shift_standard_le K N) (standard_not_le_shift K N hN) r

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K]

noncomputable def positive : K[X] →+* RatFunc K :=
  Polynomial.eval₂RingHom (algebraMap K (RatFunc K)) (uniformizer K)⁻¹

lemma eval_uniformizer (f : K[X]) :
    Polynomial.eval₂ (algebraMap K (RatFunc K)) (uniformizer K) f =
      algebraMap K[X] (RatFunc K) f := by
  exact Polynomial.eval₂_algebraMap_X f (IsScalarTower.toAlgHom K K[X] (RatFunc K))

lemma positive_mul_uniformizer (f : K[X]) :
    positive K f * uniformizer K ^ f.natDegree =
      algebraMap K[X] (RatFunc K) f.reverse := by
  let : Invertible ((uniformizer K)⁻¹) := invertibleOfNonzero (inv_ne_zero (uniformizer_ne_zero K))
  have he := Polynomial.eval₂_reverse_mul_pow (algebraMap K (RatFunc K)) ((uniformizer K)⁻¹) f
  simp only [invOf_eq_inv,inv_inv,eval_uniformizer,inv_pow] at he
  change _ = positive K f at he
  rw [← he]
  rw [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)),mul_one]

lemma positive_injective : Function.Injective (positive K) := by
  apply (injective_iff_map_eq_zero (positive K)).mpr
  intro f hf
  have he := positive_mul_uniformizer K f
  rw [hf,zero_mul] at he
  have hz : f.reverse = 0 := RatFunc.algebraMap_injective K (he.symm.trans (map_zero _).symm)
  exact Polynomial.reverse_eq_zero.mp hz

lemma positive_regular_iff (f : K[X]) (b : ℕ) :
    (∃ g : K[X], algebraMap K[X] (RatFunc K) g = positive K f * uniformizer K ^ b) ↔
      f.natDegree ≤ b := by
  constructor
  · rintro ⟨g,hg⟩
    by_cases hf : f = 0
    · simp [hf]
    by_contra hle
    have hlt : b < f.natDegree := by omega
    have he : f.reverse * Polynomial.X^b = g * Polynomial.X^f.natDegree := by
      apply RatFunc.algebraMap_injective K
      simp only [map_mul,map_pow]
      rw [hg,← positive_mul_uniformizer K f]
      unfold uniformizer
      ring
    have hc := congrArg (fun p : K[X] => p.coeff b) he
    have hright : (g*Polynomial.X^f.natDegree).coeff b = 0 := by
      rw [Polynomial.coeff_mul_X_pow']
      simp [not_le.mpr hlt]
    rw [hright] at hc
    have hleft : (f.reverse*Polynomial.X^b).coeff b = f.leadingCoeff := by
      simpa using Polynomial.coeff_mul_X_pow f.reverse b 0
    rw [hleft] at hc
    exact Polynomial.leadingCoeff_ne_zero.mpr hf hc
  · intro hf
    refine ⟨f.reverse * Polynomial.X^(b-f.natDegree),?_⟩
    rw [map_mul,map_pow,← positive_mul_uniformizer K f]
    change (positive K f * uniformizer K ^ f.natDegree) * uniformizer K ^ (b-f.natDegree) = positive K f * uniformizer K ^ b
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hf]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K]
lemma positive_zero_of_uniformizer_dvd (f g : K[X])
    (hg : uniformizer K * algebraMap K[X] (RatFunc K) g = positive K f) : f = 0 := by
  by_contra hf
  have he : f.reverse = Polynomial.X^(f.natDegree+1)*g := by
    apply RatFunc.algebraMap_injective K
    rw [← positive_mul_uniformizer K f,← hg]
    simp only [map_mul,map_pow,pow_succ]
    unfold uniformizer
    ring
  have hc := congrArg Polynomial.constantCoeff he
  have hleft : f.reverse.constantCoeff = f.leadingCoeff := by simp
  rw [hleft] at hc
  have hright : (Polynomial.X^(f.natDegree+1)*g).constantCoeff = 0 := by simp
  rw [hright] at hc
  exact Polynomial.leadingCoeff_ne_zero.mpr hf hc

lemma positive_C (c : K) : positive K (Polynomial.C c) = algebraMap K (RatFunc K) c := by
  simp [positive]
lemma positive_X : positive K Polynomial.X = (uniformizer K)⁻¹ := by simp [positive]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.Elementary CoboundaryExpanders.Patterns
variable (p n : ℕ) [Fact p.Prime]

def cutPolynomialStabilizer (cut : Fin (n+1)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n+1)) (R p)) :=
  U p (n+1) ⊓ (Matrix.GeneralLinearGroup.map (n := Fin (n+1)) (algebraMap (ZMod p) (Frac p))).range.comap (cutConjugation p n cut)

lemma polynomialStabilizer_equation (cut : Fin (n+1))
    (g : cutPolynomialStabilizer p n cut) (i j : Fin (n+1)) :
    ∃ c : ZMod p, cutPolynomial p n cut i * g.val i j =
      Polynomial.C c * cutPolynomial p n cut j := by
  obtain ⟨B,hB⟩ := g.property.2
  refine ⟨B i j, IsFractionRing.injective (R p) (Frac p) ?_⟩
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n+1)) (Frac p) => g i j) hB
  change algebraMap (ZMod p) (Frac p) (B i j) = cutConjugation p n cut g.val i j at he
  rw [cutConjugation_apply] at he
  have he' := congrArg (fun x : Frac p => x * (cutUnit p n cut j).val) he
  simp only [mul_assoc, Units.inv_val, mul_one] at he'
  rw [map_mul, map_mul, ← cutUnit_coe, ← cutUnit_coe]
  simpa only [IsScalarTower.algebraMap_apply (ZMod p) (R p) (Frac p), Polynomial.algebraMap_eq] using he'.symm

lemma polynomialStabilizer_upper (cut : Fin (n+1)) :
    cutPolynomialStabilizer p n cut ≤ cutUpper p cut := by
  intro g hg
  rw [cutUpper_iff]
  intro a b hba
  obtain ⟨c,hc⟩ := polynomialStabilizer_equation p n cut ⟨g,hg⟩ a b
  have hu : ∀ a b : Fin (n+1), b ≤ a →
      Polynomial.eval 0 (g a b) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) a b := hg.1
  unfold cutPolynomial at hc
  change (if b.val < cut.val then b.val+(n+1)-cut.val else b.val-cut.val) ≤
    (if a.val < cut.val then a.val+(n+1)-cut.val else a.val-cut.val) at hba
  have hconstant : ∀ (f : R p) (c : ZMod p), f = Polynomial.C c → b ≤ a →
      Polynomial.eval 0 f = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) a b →
      f = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (R p)) a b := by
    intro f c hf _ he
    rw [hf] at he ⊢
    simp only [Polynomial.eval_C,Matrix.one_apply] at he
    rw [he]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  by_cases ha : a.val < cut.val <;> by_cases hb : b.val < cut.val
  · rw [ite_eq_left ha,ite_eq_left hb] at hc
    have he : g a b = Polynomial.C c := mul_left_cancel₀ Polynomial.X_ne_zero
      (hc.trans (mul_comm _ _))
    have hle : b ≤ a := by simp only [ite_eq_left ha,ite_eq_left hb] at hba; change b.val ≤ a.val; omega
    exact hconstant _ _ he hle (hu a b hle)
  · rw [ite_eq_left ha,ite_eq_right hb,mul_one] at hc
    have hc0 : c = 0 := by
      have he := congrArg Polynomial.constantCoeff hc
      simpa using he.symm
    rw [hc0,Polynomial.C_0] at hc
    have hg0 : g a b = 0 := (mul_eq_zero.mp hc).resolve_left Polynomial.X_ne_zero
    rw [hg0,Matrix.one_apply,ite_eq_right (by intro he; subst b; omega)]
  · simp only [ite_eq_right ha,ite_eq_left hb] at hba
    omega
  · rw [ite_eq_right ha,ite_eq_right hb,one_mul,mul_one] at hc
    have hle : b ≤ a := by simp only [ite_eq_right ha,ite_eq_right hb] at hba; change b.val ≤ a.val; omega
    exact hconstant _ _ hc hle (hu a b hle)

lemma polynomialStabilizer_coefficient (cut : Fin (n+1))
    (g : cutPolynomialStabilizer p n cut) {a b : Fin (n+1)}
    (hlt : cutRank cut a < cutRank cut b) :
    ∃ c : ZMod p, g.val a b = pathCoefficient (p := p) (n := n) (a := a) (b := b) c := by
  obtain ⟨c,hc⟩ := polynomialStabilizer_equation p n cut g a b
  refine ⟨c,?_⟩
  unfold cutPolynomial at hc
  unfold pathCoefficient
  change (if a.val < cut.val then a.val+(n+1)-cut.val else a.val-cut.val) <
    (if b.val < cut.val then b.val+(n+1)-cut.val else b.val-cut.val) at hlt
  by_cases ha : a.val < cut.val <;> by_cases hb : b.val < cut.val
  · rw [ite_eq_left ha,ite_eq_left hb] at hc
    have hab : a.val < b.val := by simp only [ite_eq_left ha,ite_eq_left hb] at hlt; omega
    rw [ite_eq_left hab,mul_one]
    exact mul_left_cancel₀ Polynomial.X_ne_zero (hc.trans (mul_comm _ _))
  · simp only [ite_eq_left ha,ite_eq_right hb] at hlt
    omega
  · rw [ite_eq_right ha,ite_eq_left hb,one_mul] at hc
    rw [ite_eq_right (by omega : ¬ a.val < b.val)]
    exact hc
  · rw [ite_eq_right ha,ite_eq_right hb,one_mul,mul_one] at hc
    have hab : a.val < b.val := by simp only [ite_eq_right ha,ite_eq_right hb] at hlt; omega
    rw [ite_eq_left hab,mul_one]
    exact hc

theorem cutPolynomialStabilizer_eq_localGroup (hn : 1 ≤ n) (cut : Fin (n+1)) :
    cutPolynomialStabilizer p n cut = localGroup p n hn cut := by
  have hHP : localGroup p n hn cut ≤ cutPolynomialStabilizer p n cut :=
    le_inf (localGroup_le_U p n hn cut) (localGroup_le_constant p n hn cut)
  apply le_antisymm _ hHP
  let e := reindexSL (A := R p) (cutOrder cut)
  let P := (cutPolynomialStabilizer p n cut).map e.toMonoidHom
  let H := (localGroup p n hn cut).map e.toMonoidHom
  have hP : ∀ g ∈ P, Upper g := by
    rintro _ ⟨g,hg,rfl⟩
    exact polynomialStabilizer_upper p n cut hg
  have hE : ∀ g ∈ P, ∀ i j (h : i < j), E h.ne (g i j) ∈ H := by
    rintro _ ⟨g,hg,rfl⟩ i j hij
    obtain ⟨a,rfl⟩ := (cutOrder cut).surjective i
    obtain ⟨b,rfl⟩ := (cutOrder cut).surjective j
    have hab : a ≠ b := fun he => hij.ne (congrArg (cutOrder cut) he)
    obtain ⟨c,hc⟩ := polynomialStabilizer_coefficient p n cut ⟨g,hg⟩ hij
    have hmem : E hab (g a b) ∈ localGroup p n hn cut := by
      rw [hc]
      apply path_root_mem p n hn {j | j ≠ cut} hab
      intro j hj he
      subst j
      exact ((cutRank_lt_iff cut a b hab).mp hij) hj
    refine ⟨E hab (g a b),hmem,?_⟩
    change reindexSL (cutOrder cut) _ = _
    rw [reindexSL_E]
    congr 1
    exact (reindexSL_apply (cutOrder cut) g a b).symm
  have hPH := upper_subgroup_le P H (Subgroup.map_mono hHP) hP hE
  intro g hg
  obtain ⟨h,hh,he⟩ := hPH ⟨g,hg,rfl⟩
  exact e.injective he ▸ hh
end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
variable (p n : ℕ) [Fact p.Prime]
lemma mem_polynomialStabilizer_of_equations (cut : Fin (n+1))
    (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hu : g ∈ U p (n+1))
    (he : ∀ i j, ∃ c : ZMod p, cutPolynomial p n cut i * g i j =
      Polynomial.C c * cutPolynomial p n cut j) :
    g ∈ cutPolynomialStabilizer p n cut := by
  classical
  choose c hc using he
  let B : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p) := c
  have hmap : B.map (algebraMap (ZMod p) (Frac p)) = (cutConjugation p n cut g).val := by
    ext i j
    change algebraMap (ZMod p) (Frac p) (c i j) = cutConjugation p n cut g i j
    rw [cutConjugation_apply]
    have h := congrArg (algebraMap (R p) (Frac p)) (hc i j)
    simp only [map_mul,← cutUnit_coe] at h
    have hm := congrArg (fun x : Frac p => x * (cutUnit p n cut j).inv) h
    simpa only [mul_assoc,Units.val_inv, mul_one,
      IsScalarTower.algebraMap_apply (ZMod p) (R p) (Frac p), Polynomial.algebraMap_eq] using hm.symm
  have hd : B.det ≠ 0 := by
    intro hz
    have hm := congrArg Matrix.det hmap
    change ((algebraMap (ZMod p) (Frac p)).mapMatrix B).det = _ at hm
    rw [← RingHom.map_det, hz,map_zero] at hm
    exact Matrix.GeneralLinearGroup.det_ne_zero _ hm.symm
  refine ⟨hu, Matrix.GeneralLinearGroup.mk'' B (isUnit_iff_ne_zero.mpr hd), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congrFun (congrFun hmap i) j

theorem mem_localGroup_iff_cut_equations (hn : 1 ≤ n) (cut : Fin (n+1))
    (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p)) :
    g ∈ localGroup p n hn cut ↔ g ∈ U p (n+1) ∧
      ∀ i j, ∃ c : ZMod p, cutPolynomial p n cut i * g i j =
        Polynomial.C c * cutPolynomial p n cut j := by
  constructor
  · intro hg
    exact ⟨localGroup_le_U p n hn cut hg,fun i j => localGroup_entry_equation p n hn cut ⟨g,hg⟩ i j⟩
  · rintro ⟨hu,he⟩
    rw [← cutPolynomialStabilizer_eq_localGroup p n hn cut]
    exact mem_polynomialStabilizer_of_equations p n cut g hu he
end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

def cutExponent (cut i : Fin N) : ℕ := if i.val < cut.val then 1 else 0

def cutLattice (cut : Fin N) : LatticeSpace K N where
  carrier := {v | ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f * uniformizer K ^ cutExponent N cut i = v i}
  zero_mem' := fun i => ⟨0,by simp⟩
  add_mem' := by
    intro v w hv hw i
    obtain ⟨f,hf⟩ := hv i
    obtain ⟨g,hg⟩ := hw i
    exact ⟨f+g,by rw [map_add,add_mul,hf,hg]; rfl⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨f,hf⟩ := hv i
    refine ⟨a*f,?_⟩
    simp only [map_mul,mul_assoc,hf,Pi.smul_apply,Algebra.smul_def]

noncomputable def positiveMatrix (g : Matrix (Fin N) (Fin N) K[X]) : Matrix (Fin N) (Fin N) (RatFunc K) :=
  g.map (positive K)

def CutRegular (cut i j : Fin N) (f : K[X]) : Prop :=
  ∃ h : K[X], algebraMap K[X] (RatFunc K) h * uniformizer K ^ cutExponent N cut i =
    positive K f * uniformizer K ^ cutExponent N cut j

lemma preserves_cut_iff (cut : Fin N) (g : Matrix (Fin N) (Fin N) K[X]) :
    (∀ v ∈ cutLattice K N cut, (positiveMatrix K N g).mulVec v ∈ cutLattice K N cut) ↔
    ∀ i j, CutRegular K N cut i j (g i j) := by
  classical
  constructor
  · intro h i j
    let v : V K N := Pi.single j (uniformizer K ^ cutExponent N cut j)
    have hv : v ∈ cutLattice K N cut := by
      intro a
      by_cases ha : a = j
      · subst a
        exact ⟨1,by simp [v]⟩
      · exact ⟨0,by simp [v,ha]⟩
    obtain ⟨f,hf⟩ := h v hv i
    refine ⟨f,?_⟩
    simpa [v,Matrix.mulVec_single,positiveMatrix,mul_comm] using hf
  · intro h v hv i
    choose f hf using hv
    choose a ha using fun j => h i j
    refine ⟨∑ j, a j * f j,?_⟩
    simp only [map_sum,map_mul,Finset.sum_mul,Matrix.mulVec,dotProduct,positiveMatrix,Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hf j]
    calc
      _ = (algebraMap K[X] (RatFunc K) (a j) * uniformizer K ^ cutExponent N cut i) * algebraMap K[X] (RatFunc K) (f j) := by ring
      _ = _ := by rw [ha j]; ring

lemma regular_same (f : K[X]) (b : ℕ) :
    (∃ h : K[X], algebraMap K[X] (RatFunc K) h * uniformizer K ^ b = positive K f * uniformizer K ^ b) ↔
      ∃ c : K, f = Polynomial.C c := by
  constructor
  · rintro ⟨h,hh⟩
    have he := mul_right_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)) hh
    have hd := (positive_regular_iff K f 0).mp ⟨h,by simpa using he⟩
    exact ⟨f.coeff 0,Polynomial.eq_C_of_natDegree_le_zero hd⟩
  · rintro ⟨c,rfl⟩
    exact ⟨Polynomial.C c,by simp [positive_C]⟩

lemma regular_cut_equation (cut i j : Fin N) (f : K[X])
    (hzero : j.val < i.val → Polynomial.eval 0 f = 0)
    (hr : CutRegular K N cut i j f) :
    ∃ c : K, (if i.val < cut.val then (Polynomial.X : K[X]) else 1) * f =
      Polynomial.C c * (if j.val < cut.val then Polynomial.X else 1) := by
  obtain ⟨h,hh⟩ := hr
  by_cases hi : i.val < cut.val <;> by_cases hj : j.val < cut.val
  · simp only [cutExponent,ite_eq_left hi,ite_eq_left hj,pow_one] at hh
    obtain ⟨c,hc⟩ := (regular_same K f 1).mp ⟨h,by simpa using hh⟩
    exact ⟨c,by rw [ite_eq_left hi,ite_eq_left hj,hc,mul_comm]⟩
  · simp only [cutExponent,ite_eq_left hi,ite_eq_right hj,pow_one,pow_zero,mul_one] at hh
    have hf : f = 0 := positive_zero_of_uniformizer_dvd K f h (by simpa only [mul_comm] using hh)
    exact ⟨0,by simp [hf]⟩
  · simp only [cutExponent,ite_eq_right hi,ite_eq_left hj,pow_one,pow_zero,mul_one] at hh
    have hd := (positive_regular_iff K f 1).mp ⟨h,by simpa using hh⟩
    have hz : f.coeff 0 = 0 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hzero (by omega)
    have hf := Polynomial.eq_X_add_C_of_natDegree_le_one hd
    rw [hz,Polynomial.C_0,add_zero] at hf
    exact ⟨f.coeff 1,by simpa only [ite_eq_right hi,ite_eq_left hj,one_mul] using hf⟩
  · simp only [cutExponent,ite_eq_right hi,ite_eq_right hj,pow_zero,mul_one] at hh
    obtain ⟨c,hc⟩ := (regular_same K f 0).mp ⟨h,by simpa using hh⟩
    exact ⟨c,by simp [hi,hj,hc]⟩

lemma regular_of_cut_equation (cut i j : Fin N) (f : K[X]) (c : K)
    (hc : (if i.val < cut.val then (Polynomial.X : K[X]) else 1) * f =
      Polynomial.C c * (if j.val < cut.val then Polynomial.X else 1)) :
    CutRegular K N cut i j f := by
  have he := congrArg (positive K) hc
  simp only [map_mul,apply_ite,map_one,positive_X,positive_C] at he
  refine ⟨Polynomial.C c,?_⟩
  have hC : algebraMap K[X] (RatFunc K) (Polynomial.C c) = algebraMap K (RatFunc K) c := by
    exact (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c).symm
  rw [hC]
  by_cases hi : i.val < cut.val <;> by_cases hj : j.val < cut.val
  · simp only [ite_eq_left hi,ite_eq_left hj] at he
    simp only [cutExponent,ite_eq_left hi,ite_eq_left hj,pow_one]
    have he' : positive K f = algebraMap K (RatFunc K) c := by
      apply mul_left_cancel₀ (inv_ne_zero (uniformizer_ne_zero K))
      simpa only [mul_comm] using he
    rw [he']
  · simp only [ite_eq_left hi,ite_eq_right hj,mul_one] at he
    simp only [cutExponent,ite_eq_left hi,ite_eq_right hj,pow_one,pow_zero,mul_one]
    rw [← he]
    field_simp [uniformizer_ne_zero K]
  · simp only [ite_eq_right hi,ite_eq_left hj,one_mul] at he
    simp only [cutExponent,ite_eq_right hi,ite_eq_left hj,pow_one,pow_zero,mul_one]
    rw [he,mul_assoc,inv_mul_cancel₀ (uniformizer_ne_zero K),mul_one]
  · simp only [ite_eq_right hi,ite_eq_right hj,one_mul,mul_one] at he
    simpa only [cutExponent,ite_eq_right hi,ite_eq_right hj,pow_zero,mul_one] using he.symm

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices
variable (p n : ℕ) [Fact p.Prime]

theorem preserves_cutLattice_iff_localGroup (hn : 1 ≤ n) (cut : Fin (n+1))
    (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p)) (hu : g ∈ U p (n+1)) :
    (∀ v ∈ cutLattice (ZMod p) (n+1) cut,
      (positiveMatrix (ZMod p) (n+1) g.val).mulVec v ∈ cutLattice (ZMod p) (n+1) cut) ↔
      g ∈ localGroup p n hn cut := by
  rw [preserves_cut_iff,mem_localGroup_iff_cut_equations]
  constructor
  · intro h
    refine ⟨hu,fun i j => ?_⟩
    apply regular_cut_equation (ZMod p) (n+1) cut i j (g i j) _ (h i j)
    intro hji
    have he := hu i j (show j ≤ i from le_of_lt hji)
    change Polynomial.eval 0 (g i j) = _ at he
    simpa only [Matrix.one_apply,ite_eq_right (show i ≠ j by intro h; subst j; omega)] using he
  · rintro ⟨_,h⟩ i j
    obtain ⟨c,hc⟩ := h i j
    exact regular_of_cut_equation (ZMod p) (n+1) cut i j (g i j) c hc
end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

lemma cut_le_standard (cut : Fin N) : cutLattice K N cut ≤ standard K N := by
  intro v hv i
  obtain ⟨f,hf⟩ := hv i
  exact ⟨f * Polynomial.X ^ cutExponent N cut i,by simpa only [map_mul,map_pow,uniformizer] using hf⟩

lemma shift_standard_le_cut (cut : Fin N) : shift K N (standard K N) ≤ cutLattice K N cut := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
  intro i
  obtain ⟨f,hf⟩ := hw i
  by_cases hi : i.val < cut.val
  · exact ⟨f,by simp only [cutExponent,ite_eq_left hi,pow_one,hf,shiftLinear_apply,mul_comm]⟩
  · exact ⟨Polynomial.X*f,by simp only [cutExponent,ite_eq_right hi,pow_zero,mul_one,map_mul,hf,shiftLinear_apply,uniformizer]⟩

lemma uniformizer_mul_ne_one (f : K[X]) : uniformizer K * algebraMap K[X] (RatFunc K) f ≠ 1 := by
  intro hf
  have hp : Polynomial.X * f = 1 := RatFunc.algebraMap_injective K (by simpa only [map_mul,map_one,uniformizer] using hf)
  have hz := congrArg Polynomial.constantCoeff hp
  simp at hz

lemma single_mem_cut (cut : Fin N) : Pi.single cut (1 : RatFunc K) ∈ cutLattice K N cut := by
  intro i
  by_cases hi : i = cut
  · subst i
    exact ⟨1,by simp [cutExponent]⟩
  · exact ⟨0,by simp [hi]⟩

lemma cut_not_le_shift (cut : Fin N) : ¬ cutLattice K N cut ≤ shift K N (standard K N) := by
  intro hle
  obtain ⟨w,hw,he⟩ := (mem_shift K N _ _).mp (hle (single_mem_cut K N cut))
  obtain ⟨f,hf⟩ := hw cut
  apply uniformizer_mul_ne_one K f
  simpa only [shiftLinear_apply,Pi.single_eq_same,hf] using congr_fun he cut

lemma cut_antitone : Antitone (cutLattice K N) := by
  intro a b hab v hv i
  by_cases hi : i.val < a.val
  · obtain ⟨f,hf⟩ := hv i
    exact ⟨f,by simpa only [cutExponent,ite_eq_left hi,ite_eq_left (show i.val < b.val by omega)] using hf⟩
  · obtain ⟨f,hf⟩ := (cut_le_standard K N b hv) i
    exact ⟨f,by simpa only [cutExponent,ite_eq_right hi,pow_zero,mul_one] using hf⟩

lemma cut_le_cut_iff (a b : Fin N) : cutLattice K N a ≤ cutLattice K N b ↔ b ≤ a := by
  constructor
  · intro hle
    by_contra hba
    have hab : a.val < b.val := lt_of_not_ge hba
    obtain ⟨f,hf⟩ := hle (single_mem_cut K N a) a
    apply uniformizer_mul_ne_one K f
    simpa only [cutExponent,ite_eq_left hab,pow_one,Pi.single_eq_same,mul_comm] using hf
  · intro hba; exact cut_antitone K N hba

lemma cut_injective : Function.Injective (cutLattice K N) := by
  intro a b he
  exact le_antisymm ((cut_le_cut_iff K N b a).mp he.ge) ((cut_le_cut_iff K N a b).mp he.le)

noncomputable def cutVertex (cut : Fin N) : Vertex K N :=
  ⟨cutLattice K N cut,cut_le_standard K N cut,cut_not_le_shift K N cut,
    ⟨1,shift_standard_le_cut K N cut⟩,shift_le_self K N _⟩

lemma cutVertex_injective : Function.Injective (cutVertex K N) := by
  intro a b he
  exact cut_injective K N (congrArg Subtype.val he)

noncomputable def baseChamber : Finset (Vertex K N) :=
  Finset.univ.image (cutVertex K N)

lemma baseChamber_face : baseChamber K N ∈ (building K N).faces := by
  constructor
  · intro A hA B hB
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
    rcases le_total a b with hab | hba
    · exact Or.inr (cut_antitone K N hab)
    · exact Or.inl (cut_antitone K N hba)
  · intro A hA B hB
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
    exact ((shift K N).monotone (cut_le_standard K N a)).trans (shift_standard_le_cut K N b)

lemma baseChamber_card : (baseChamber K N).card = N := by
  rw [baseChamber,Finset.card_image_of_injective _ (cutVertex_injective K N),Finset.card_univ,Fintype.card_fin]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

noncomputable def iterIso : ℕ → P ≃o P
  | 0 => OrderIso.refl P
  | m+1 => (iterIso m).trans T

@[simp] lemma iterIso_apply (m : ℕ) (A : P) : iterIso T m A = level T A m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg T ih

lemma level_map (A : P) (m : ℕ) : level T (T A) m = T (level T A m) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg T ih

lemma level_add (A : P) (a b : ℕ) : level T A (a+b) = level T (level T A a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg T ih

lemma level_mono (m : ℕ) {A B : P} (h : A ≤ B) : level T A m ≤ level T B m :=
  by simpa only [iterIso_apply] using (iterIso T m).monotone h

lemma level_injective (m : ℕ) : Function.Injective (fun A => level T A m) :=
  by
    intro A B he
    apply (iterIso T m).injective
    simpa only [iterIso_apply] using he

lemma level_reflect_le (m : ℕ) (A B : P) : level T A m ≤ level T B m ↔ A ≤ B :=
  by simpa only [iterIso_apply] using ((iterIso T m).le_iff_le (x := A) (y := B))

lemma exists_normalized (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (m : ℕ)
    (B : P) (hBC : B ≤ C) (hlow : level T C m ≤ B) (hB : T B ≤ B) :
    ∃ A : Vertex T C, ∃ j : ℕ, j ≤ m ∧ B = level T A.val j := by
  induction m generalizing B with
  | zero =>
    have he : B = C := le_antisymm hBC hlow
    subst B
    exact ⟨base T C hC hstrict,0,le_rfl,rfl⟩
  | succ m ih =>
    by_cases hb : B ≤ T C
    · have hBC' : T.symm B ≤ C := by
        simpa only [T.symm_apply_apply] using T.symm.monotone hb
      have hlow' : level T C m ≤ T.symm B := by
        simpa only [level_succ,T.symm_apply_apply] using T.symm.monotone hlow
      have hB' : T (T.symm B) ≤ T.symm B := by
        simpa only [T.apply_symm_apply,T.symm_apply_apply] using T.symm.monotone hB
      obtain ⟨A,j,hj,he⟩ := ih (T.symm B) hBC' hlow' hB'
      refine ⟨A,j+1,by omega,?_⟩
      simpa only [T.apply_symm_apply,level_succ] using congrArg T he
    · exact ⟨⟨B,hBC,hb,⟨m+1,hlow⟩,hB⟩,0,Nat.zero_le _,rfl⟩

lemma level_vertex_le (A : Vertex T C) (m : ℕ) : level T A.val m ≤ level T C m :=
  level_mono T m (vertex_le T C A)

lemma normalized_unique (hC : T C ≤ C) (A B : Vertex T C) (a b : ℕ)
    (he : level T A.val a = level T B.val b) : A = B ∧ a = b := by
  have hle : ∀ {A B : Vertex T C} {a b : ℕ}, a ≤ b →
      level T A.val a = level T B.val b → a = b := by
    intro A B a b hab he
    obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
    have he' : A.val = level T B.val c := by
      apply level_injective T a
      dsimp only
      rw [← level_add, Nat.add_comm c a]
      exact he
    cases c with
    | zero => simp
    | succ c =>
      exfalso
      apply vertex_normalized T C A
      rw [he']
      exact (level_vertex_le T C B (c+1)).trans
        (level_antitone T C hC (show 1 ≤ c+1 by omega))
  have hab : a = b := by
    rcases le_total a b with h | h
    · exact hle h he
    · exact (hle h he.symm).symm
  subst b
  exact ⟨Subtype.ext (level_injective T a he),rfl⟩

def Homothetic (A B : P) : Prop := ∃ a b : ℕ, level T A a = level T B b

lemma homothetic_refl (A : P) : Homothetic T A A := ⟨0,0,rfl⟩
lemma homothetic_symm {A B : P} : Homothetic T A B → Homothetic T B A := by
  rintro ⟨a,b,h⟩; exact ⟨b,a,h.symm⟩
lemma homothetic_trans {A B D : P} : Homothetic T A B → Homothetic T B D → Homothetic T A D := by
  rintro ⟨a,b,h₁⟩ ⟨c,d,h₂⟩
  refine ⟨a+c,d+b,?_⟩
  rw [level_add,level_add,h₁,← level_add,Nat.add_comm b c,level_add,h₂]

lemma homothetic_normalized_iff (hC : T C ≤ C) (A B : Vertex T C) :
    Homothetic T A.val B.val ↔ A = B := by
  constructor
  · rintro ⟨a,b,h⟩
    exact (normalized_unique T C hC A B a b h).1
  · rintro rfl
    exact homothetic_refl T _

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma level_swap (A : P) (a b : ℕ) : level T (level T A a) b = level T (level T A b) a := by
  rw [← level_add,← level_add,Nat.add_comm]

lemma normalized_level_le (hC : T C ≤ C) (A B : Vertex T C) (a b : ℕ)
    (hle : level T A.val a ≤ level T B.val b) : b ≤ a := by
  by_contra h
  have hab : a < b := by omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hab)
  subst b
  have ha : A.val ≤ level T B.val d := by
    apply (level_reflect_le T a _ _).mp
    rw [← level_add,Nat.add_comm d a]
    exact hle
  apply vertex_normalized T C A
  exact ha.trans ((level_vertex_le T C B d).trans
    (level_antitone T C hC (show 1 ≤ d by omega)))

def Compatible (A B : P) : Prop :=
  ∃ a b : ℕ, T (level T A a) ≤ level T B b ∧ level T B b ≤ level T A a

lemma compatible_symm {A B : P} (h : Compatible T A B) : Compatible T B A := by
  obtain ⟨a,b,hab,hba⟩ := h
  exact ⟨b,a+1,T.monotone hba,hab⟩

lemma compatible_homothetic_left {A A' B : P} (hA : Homothetic T A A')
    (h : Compatible T A B) : Compatible T A' B := by
  obtain ⟨r,s,he⟩ := hA
  obtain ⟨a,b,hab,hba⟩ := h
  have he' : level T A' (a+s) = level T A (a+r) := by
    rw [Nat.add_comm a s,level_add,← he,← level_add,Nat.add_comm r a]
  refine ⟨a+s,b+r,?_,?_⟩
  · rw [he',level_add,level_add,← level_map]
    exact level_mono T r hab
  · rw [he',level_add,level_add]
    exact level_mono T r hba

lemma compatible_homothetic {A A' B B' : P} (hA : Homothetic T A A')
    (hB : Homothetic T B B') (h : Compatible T A B) : Compatible T A' B' :=
  compatible_symm T (compatible_homothetic_left T hB
    (compatible_symm T (compatible_homothetic_left T hA h)))

lemma compatible_normalized_iff (hC : T C ≤ C) (A B : Vertex T C) :
    Compatible T A.val B.val ↔ (A ≤ B ∨ B ≤ A) ∧ T A.val ≤ B.val ∧ T B.val ≤ A.val := by
  constructor
  · rintro ⟨a,b,hab,hba⟩
    have h₁ : a ≤ b := normalized_level_le T C hC B A b a hba
    have h₂ : b ≤ a+1 := normalized_level_le T C hC A B (a+1) b hab
    have hc : b = a ∨ b = a+1 := by omega
    rcases hc with he | he
    · rw [he] at hab hba
      have hBA : B.val ≤ A.val := (level_reflect_le T a _ _).mp hba
      have hAB : T A.val ≤ B.val := by
        apply (level_reflect_le T a _ _).mp
        rwa [level_map]
      exact ⟨Or.inr hBA,hAB,(T.monotone hBA).trans (vertex_shift_le T C A)⟩
    · rw [he] at hab hba
      have hAB : A.val ≤ B.val := (level_reflect_le T (a+1) _ _).mp hab
      have hBA : T B.val ≤ A.val := by
        apply (level_reflect_le T a _ _).mp
        rwa [level_map]
      exact ⟨Or.inl hAB,(T.monotone hAB).trans (vertex_shift_le T C B),hBA⟩
  · rintro ⟨hcmp,hab,hba⟩
    rcases hcmp with hAB | hBA
    · exact compatible_symm T ⟨0,0,hba,hAB⟩
    · exact ⟨0,0,hab,hBA⟩

lemma isFace_iff_compatible (hC : T C ≤ C) (s : Finset (Vertex T C)) :
    IsFace T C s ↔ ∀ A ∈ s, ∀ B ∈ s, Compatible T A.val B.val := by
  constructor
  · intro h A hA B hB
    exact (compatible_normalized_iff T C hC A B).mpr
      ⟨h.1 A hA B hB,h.2 A hA B hB,h.2 B hB A hA⟩
  · intro h
    exact ⟨fun A hA B hB => ((compatible_normalized_iff T C hC A B).mp (h A hA B hB)).1,
      fun A hA B hB => ((compatible_normalized_iff T C hC A B).mp (h A hA B hB)).2.1⟩

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma map_level (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A)) (A : P) (m : ℕ) :
    S (level T A m) = level T (S A) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [level_succ,hS,ih,level_succ]

lemma homothetic_map (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A))
    {A B : P} (h : Homothetic T A B) : Homothetic T (S A) (S B) := by
  obtain ⟨a,b,he⟩ := h
  exact ⟨a,b,by simpa only [map_level T S hS] using congrArg S he⟩

lemma homothetic_map_iff (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A))
    (A B : P) : Homothetic T (S A) (S B) ↔ Homothetic T A B := by
  constructor
  · rintro ⟨a,b,he⟩
    refine ⟨a,b,S.injective ?_⟩
    simpa only [map_level T S hS] using he
  · exact homothetic_map T S hS

lemma compatible_map (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A))
    {A B : P} (h : Compatible T A B) : Compatible T (S A) (S B) := by
  obtain ⟨a,b,hab,hba⟩ := h
  refine ⟨a,b,?_,?_⟩
  · simpa only [hS,map_level T S hS] using S.monotone hab
  · simpa only [map_level T S hS] using S.monotone hba

lemma exists_mapVertex (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hupper : ∃ r, level T (S C) r ≤ C) (hlower : ∃ s, level T C s ≤ S C)
    (A : Vertex T C) : ∃ B : Vertex T C, Homothetic T (S A.val) B.val := by
  obtain ⟨r,hr⟩ := hupper
  obtain ⟨s,hs⟩ := hlower
  obtain ⟨m,hm⟩ := vertex_bounded T C A
  have hu : level T (S A.val) r ≤ C :=
    (level_mono T r (S.monotone (vertex_le T C A))).trans hr
  have hl : level T C (s+m) ≤ S A.val := by
    rw [level_add]
    exact (level_mono T m hs).trans (by
      rw [← map_level T S hS]
      exact S.monotone hm)
  have hb : T (S A.val) ≤ S A.val := by
    rw [← hS]
    exact S.monotone (vertex_shift_le T C A)
  have hl' : level T C (s+m+r) ≤ level T (S A.val) r := by
    rw [level_add]
    exact level_mono T r hl
  have hb' : T (level T (S A.val) r) ≤ level T (S A.val) r := by
    rw [← level_map]
    exact level_mono T r hb
  obtain ⟨B,j,_,he⟩ := exists_normalized T C hC hstrict (s+m+r) _ hu hl' hb'
  exact ⟨B,r,j,he⟩

noncomputable def mapVertex (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C)
    (A : Vertex T C) : Vertex T C :=
  (exists_mapVertex T C hC hstrict S hS hu hl A).choose

lemma mapVertex_homothetic (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C)
    (A : Vertex T C) : Homothetic T (S A.val) (mapVertex T C hC hstrict S hS hu hl A).val :=
  (exists_mapVertex T C hC hstrict S hS hu hl A).choose_spec

lemma mapVertex_injective (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C) :
    Function.Injective (mapVertex T C hC hstrict S hS hu hl) := by
  intro A B he
  have hA := mapVertex_homothetic T C hC hstrict S hS hu hl A
  have hB := mapVertex_homothetic T C hC hstrict S hS hu hl B
  rw [he] at hA
  exact (homothetic_normalized_iff T C hC A B).mp ((homothetic_map_iff T S hS _ _).mp
    (homothetic_trans T hA (homothetic_symm T hB)))

lemma mapVertex_face (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C)
    (s : Finset (Vertex T C)) (hs : IsFace T C s) :
    IsFace T C (s.image (mapVertex T C hC hstrict S hS hu hl)) := by
  apply (isFace_iff_compatible T C hC _).mpr
  intro A hA B hB
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
  exact compatible_homothetic T (mapVertex_homothetic T C hC hstrict S hS hu hl a)
    (mapVertex_homothetic T C hC hstrict S hS hu hl b)
    (compatible_map T S hS ((isFace_iff_compatible T C hC s).mp hs a ha b hb))

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open Module
variable (K : Type) [Field K] (N : ℕ)

noncomputable def polynomialToStandard : (Fin N → K[X]) →ₗ[K[X]] standard K N where
  toFun f := ⟨fun i => algebraMap K[X] (RatFunc K) (f i),fun i => ⟨f i,rfl⟩⟩
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp [Algebra.smul_def]

lemma polynomialToStandard_bijective : Function.Bijective (polynomialToStandard K N) := by
  constructor
  · intro f g he
    funext i
    exact RatFunc.algebraMap_injective K (congr_fun (congrArg Subtype.val he) i)
  · intro v
    choose f hf using v.property
    refine ⟨f,?_⟩
    apply Subtype.ext
    exact funext hf

noncomputable def standardEquiv : (Fin N → K[X]) ≃ₗ[K[X]] standard K N :=
  LinearEquiv.ofBijective (polynomialToStandard K N) (polynomialToStandard_bijective K N)

noncomputable def standardBasis : Basis (Fin N) K[X] (standard K N) :=
  (Pi.basisFun K[X] (Fin N)).map (standardEquiv K N)

lemma shiftLinear_eq_smul (v : V K N) : shiftLinear K N v = (Polynomial.X : K[X]) • v := by
  ext i
  simp only [shiftLinear_apply,Pi.smul_apply,Algebra.smul_def,uniformizer]

lemma smul_pow_mem_level (m : ℕ) (v : V K N) (hv : v ∈ standard K N) :
    (Polynomial.X^m : K[X]) • v ∈ AffineLattices.level (shift K N) (standard K N) m := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    apply (mem_shift K N _ _).mpr
    refine ⟨(Polynomial.X^m : K[X]) • v,ih,?_⟩
    rw [shiftLinear_eq_smul,smul_smul,pow_succ']

noncomputable def boundedBasis (A : Vertex K N) : Σ r : ℕ, Basis (Fin r) K[X] (A.val) :=
  Submodule.basisOfPidOfLE (AffineLattices.vertex_le _ _ A) (standardBasis K N)

lemma boundedBasis_rank (A : Vertex K N) : (boundedBasis K N A).1 = N := by
  let b := (boundedBasis K N A).2
  let : Module.Free K[X] A.val := Module.Free.of_basis b
  let : Module.Finite K[X] A.val := Module.Finite.of_basis b
  let : Module.Free K[X] (standard K N) := Module.Free.of_basis (standardBasis K N)
  let : Module.Finite K[X] (standard K N) := Module.Finite.of_basis (standardBasis K N)
  have hstd : Module.finrank K[X] (standard K N) = N := by
    simpa using Module.finrank_eq_card_basis (standardBasis K N)
  have hA : Module.finrank K[X] A.val = (boundedBasis K N A).1 := by
    simpa using Module.finrank_eq_card_basis b
  have hle := LinearMap.finrank_le_finrank_of_injective
    (Submodule.inclusion_injective (AffineLattices.vertex_le _ _ A))
  obtain ⟨m,hm⟩ := AffineLattices.vertex_bounded _ _ A
  let f : standard K N →ₗ[K[X]] A.val :=
    { toFun := fun v => ⟨(Polynomial.X^m : K[X]) • v.val,hm (smul_pow_mem_level K N m v.val v.property)⟩
      map_add' := by intros; ext; simp [smul_add]
      map_smul' := by intros; ext; simp [smul_smul,mul_comm] }
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    have he' : (Polynomial.X^m : K[X]) • v.val = (Polynomial.X^m : K[X]) • w.val := congrArg Subtype.val he
    ext i
    have hei := congr_fun he' i
    simp only [Pi.smul_apply,Algebra.smul_def,map_pow] at hei
    exact mul_left_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)) hei
  have hge := LinearMap.finrank_le_finrank_of_injective hf
  rw [hstd,hA] at hle hge
  exact le_antisymm hle hge

noncomputable def latticeBasis (A : Vertex K N) : Basis (Fin N) K[X] A.val :=
  (boundedBasis K N A).2.reindex (finCongr (boundedBasis_rank K N A))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open Module
variable (K : Type) [Field K] (N : ℕ)

noncomputable def constantVector : (Fin N → K[X]) →ₗ[K] (Fin N → K) where
  toFun f i := (f i).coeff 0
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp

noncomputable def residueMap (A : Vertex K N) : A.val →ₗ[K] (Fin N → K) :=
  (constantVector K N).comp ((latticeBasis K N A).equivFun.restrictScalars K).toLinearMap

lemma residueMap_apply (A : Vertex K N) (v : A.val) (i : Fin N) :
    residueMap K N A v i = (((latticeBasis K N A).equivFun v) i).coeff 0 := rfl

lemma residueMap_surjective (A : Vertex K N) : Function.Surjective (residueMap K N A) := by
  intro v
  refine ⟨(latticeBasis K N A).equivFun.symm (fun i => Polynomial.C (v i)),?_⟩
  ext i
  simp only [residueMap_apply,LinearEquiv.apply_symm_apply,Polynomial.coeff_C_zero]

lemma residueMap_smul_polynomial (A : Vertex K N) (f : K[X]) (v : A.val) :
    residueMap K N A (f • v) = f.coeff 0 • residueMap K N A v := by
  ext i
  simp only [residueMap_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  change Polynomial.constantCoeff (f * _) = Polynomial.constantCoeff f * Polynomial.constantCoeff _
  exact map_mul _ _ _

lemma residueMap_eq_zero_iff (A : Vertex K N) (v : A.val) :
    residueMap K N A v = 0 ↔ v.val ∈ shift K N A.val := by
  constructor
  · intro h
    have hz : ∀ i, Polynomial.X ∣ (latticeBasis K N A).equivFun v i := by
      intro i
      apply Polynomial.X_dvd_iff.mpr
      exact congr_fun h i
    choose f hf using hz
    let w : A.val := (latticeBasis K N A).equivFun.symm f
    have he : (Polynomial.X : K[X]) • w = v := by
      apply (latticeBasis K N A).equivFun.injective
      simp only [map_smul,LinearEquiv.apply_symm_apply,w]
      funext i
      exact (hf i).symm
    apply (mem_shift K N _ _).mpr
    refine ⟨w.val,w.property,?_⟩
    have hv := congrArg Subtype.val he
    change (Polynomial.X : K[X]) • w.val = v.val at hv
    simpa only [shiftLinear_eq_smul] using hv
  · intro hv
    obtain ⟨w,hw,he⟩ := (mem_shift K N _ _).mp hv
    have he' : (Polynomial.X : K[X]) • (⟨w,hw⟩ : A.val) = v := by
      apply Subtype.ext
      change (Polynomial.X : K[X]) • w = v.val
      simpa only [shiftLinear_eq_smul] using he
    rw [← he',residueMap_smul_polynomial]
    simp

noncomputable def residueKernel (A : Vertex K N) : Submodule K A.val :=
  ((shift K N A.val).restrictScalars K).comap (A.val.subtype.restrictScalars K)

lemma residueKernel_eq (A : Vertex K N) : residueKernel K N A = (residueMap K N A).ker := by
  ext v
  exact (residueMap_eq_zero_iff K N A v).symm

noncomputable def residueEquiv (A : Vertex K N) :
    (A.val ⧸ residueKernel K N A) ≃ₗ[K] (Fin N → K) := by
  rw [residueKernel_eq]
  exact (residueMap K N A).quotKerEquivOfSurjective (residueMap_surjective K N A)

lemma residue_finrank (A : Vertex K N) : Module.finrank K (A.val ⧸ residueKernel K N A) = N := by
  rw [(residueEquiv K N A).finrank_eq]
  simp

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma mem_level (A : LatticeSpace K N) (m : ℕ) (v : V K N) :
    v ∈ level (shift K N) A m ↔ ∃ w ∈ A, (Polynomial.X^m : K[X]) • w = v := by
  induction m generalizing v with
  | zero => simp [level]
  | succ m ih =>
    rw [level_succ,mem_shift]
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,hw,rfl⟩ := (ih z).mp hz
      exact ⟨w,hw,by rw [shiftLinear_eq_smul,smul_smul,pow_succ']⟩
    · rintro ⟨w,hw,rfl⟩
      refine ⟨(Polynomial.X^m : K[X]) • w,(ih _).mpr ⟨w,hw,rfl⟩,?_⟩
      rw [shiftLinear_eq_smul,smul_smul,pow_succ']

noncomputable def positiveLinear (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    V K N ≃ₗ[K[X]] V K N :=
  (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (positive K) g)).restrictScalars K[X]

lemma positiveLinear_apply (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (v : V K N) :
    positiveLinear K N g v = (positiveMatrix K N g.val).mulVec v := rfl

lemma positiveLinear_mul (g h : Matrix.SpecialLinearGroup (Fin N) K[X]) (v : V K N) :
    positiveLinear K N (g*h) v = positiveLinear K N g (positiveLinear K N h v) := by
  simp only [positiveLinear,map_mul,LinearEquiv.mul_apply,LinearEquiv.restrictScalars_apply]

@[simp] lemma positiveLinear_one (v : V K N) :
    positiveLinear K N 1 v = v := by
  simp [positiveLinear]

lemma positiveLinear_inv (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    positiveLinear K N g⁻¹ = (positiveLinear K N g).symm := by
  apply LinearEquiv.ext
  intro v
  apply (positiveLinear K N g).injective
  rw [← positiveLinear_mul,mul_inv_cancel,positiveLinear_one,LinearEquiv.apply_symm_apply]

lemma positiveLinear_shift (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (v : V K N) :
    positiveLinear K N g (shiftLinear K N v) = shiftLinear K N (positiveLinear K N g v) := by
  rw [shiftLinear_eq_smul,shiftLinear_eq_smul,map_smul]

noncomputable def positiveAction (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    LatticeSpace K N ≃o LatticeSpace K N := Submodule.orderIsoMapComap (positiveLinear K N g)

lemma mem_positiveAction (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : LatticeSpace K N)
    (v : V K N) : v ∈ positiveAction K N g A ↔ ∃ w ∈ A, positiveLinear K N g w = v :=
  Submodule.mem_map

lemma positiveAction_inv (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    positiveAction K N g⁻¹ = (positiveAction K N g).symm := by
  apply OrderIso.ext
  funext A
  rw [positiveAction,positiveLinear_inv,positiveAction,Submodule.orderIsoMapComap_symm_apply']
  rfl

lemma positiveAction_shift (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : LatticeSpace K N) :
    positiveAction K N g (shift K N A) = shift K N (positiveAction K N g A) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_positiveAction K N g _ _).mp hv
    obtain ⟨z,hz,rfl⟩ := (mem_shift K N _ _).mp hw
    exact (mem_shift K N _ _).mpr ⟨positiveLinear K N g z,
      (mem_positiveAction K N g _ _).mpr ⟨z,hz,rfl⟩,(positiveLinear_shift K N g z).symm⟩
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_shift K N _ _).mp hv
    obtain ⟨z,hz,rfl⟩ := (mem_positiveAction K N g _ _).mp hw
    exact (mem_positiveAction K N g _ _).mpr ⟨shiftLinear K N z,
      (mem_shift K N _ _).mpr ⟨z,hz,rfl⟩,positiveLinear_shift K N g z⟩

lemma positiveAction_upper (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    ∃ r, level (shift K N) (positiveAction K N g (standard K N)) r ≤ standard K N := by
  classical
  let r := Finset.univ.sup (fun i : Fin N => Finset.univ.sup (fun j : Fin N => (g i j).natDegree))
  have hr : ∀ i j, (g i j).natDegree ≤ r := by
    intro i j
    exact (Finset.le_sup (f := fun j : Fin N => (g i j).natDegree) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i : Fin N => Finset.univ.sup (fun j : Fin N => (g i j).natDegree)) (Finset.mem_univ i))
  refine ⟨r,?_⟩
  intro v hv
  obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
  obtain ⟨z,hz,rfl⟩ := (mem_positiveAction K N g _ _).mp hw
  choose f hf using hz
  intro i
  choose a ha using fun j => (positive_regular_iff K (g i j) r).mpr (hr i j)
  refine ⟨∑ j, a j * f j,?_⟩
  simp only [map_sum,map_mul,positiveLinear_apply,Pi.smul_apply,Algebra.smul_def,
    map_pow,Matrix.mulVec,dotProduct,
    positiveMatrix,Matrix.map_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j,hf j]
  change (positive K (g i j) * uniformizer K ^ r) * z j =
    uniformizer K ^ r * (positive K (g i j) * z j)
  ring

lemma positiveAction_lower (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    ∃ s, level (shift K N) (standard K N) s ≤ positiveAction K N g (standard K N) := by
  obtain ⟨s,hs⟩ := positiveAction_upper K N g⁻¹
  refine ⟨s,?_⟩
  have hm := (positiveAction K N g).monotone hs
  rw [map_level _ _ (positiveAction_shift K N g),positiveAction_inv,
    OrderIso.apply_symm_apply] at hm
  exact hm

noncomputable def actVertex (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    Vertex K N → Vertex K N :=
  mapVertex (shift K N) (standard K N) (shift_standard_le K N) (standard_not_le_shift K N hN)
    (positiveAction K N g) (positiveAction_shift K N g) (positiveAction_upper K N g) (positiveAction_lower K N g)

lemma actVertex_homothetic (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : Vertex K N) :
    Homothetic (shift K N) (positiveAction K N g A.val) (actVertex K N hN g A).val :=
  mapVertex_homothetic _ _ _ _ _ _ _ _ _

lemma actVertex_face (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X])
    (s : Finset (Vertex K N)) (hs : s ∈ (building K N).faces) :
    s.image (actVertex K N hN g) ∈ (building K N).faces :=
  mapVertex_face _ _ _ _ _ _ _ _ s hs

end CoboundaryExpanders.RationalLattices

end

end OAI
