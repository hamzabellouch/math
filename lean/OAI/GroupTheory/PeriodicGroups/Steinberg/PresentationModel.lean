import Mathlib
import OAI.GroupTheory.PeriodicGroups.Algebra.MatrixTests

namespace OAI

section
universe u v w
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)
abbrev Token := {t : List (Codec.Raw h) // Codec.rawToken (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) t}
instance token_finite : Finite (A.Token hh) := (Codec.finite_rawTokens (hh:=A.height_pos hh) (S:=A.schedule h hh) (d:=10000*(D*h))).to_subtype
instance token_fintype : Fintype (A.Token hh) := Fintype.ofFinite _
def normal (t : A.Token hh) : List (Codec.Raw (D*h)) :=
  Classical.choose (Codec.rawToken_normalize (A.threshold_four.trans hh) (A.fits h hh).2.2.2.1 t.property)
lemma normal_spec (t : A.Token hh) :
    1 ≤ (A.normal hh t).length ∧ (A.normal hh t).length ≤ 10 ∧
      t.val.length=(2*(2^h)+1)*(A.normal hh t).length ∧
      Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) t.val (embedding h D (A.normal hh t)) :=
  Classical.choose_spec (Codec.rawToken_normalize (A.threshold_four.trans hh) (A.fits h hh).2.2.2.1 t.property)
lemma normal_word (K : Type*) [CommRing K] (t : A.Token hh) :
    (A.table h hh).word (K:=K) (FreeMonoid.ofList t.val)=
      A.embeddingHom K hh ((A.table (D*h) (A.next_large hh)).word (FreeMonoid.ofList (A.normal hh t))) := by
  rw [A.embeddingHom_word]
  exact (A.table h hh).word_reach (Codec.reach_iff_table.mp (A.normal_spec hh t).2.2.2)
def letters (K : Type*) [CommRing K] : Codec.Raw h → A.Algebra K h hh :=
  Codec.letter (A.height_pos hh) (A.schedule h hh) (10000*(D*h))
lemma eval_letters (K : Type*) [CommRing K] (w : List (Codec.Raw h)) :
    DirectCancellation.eval (A.letters hh K) w=(A.table h hh).word (FreeMonoid.ofList w) :=
  Codec.eval_letter w

theorem cut_reduction (K : Type*) [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Codec.Raw h → Matrix ι ι K)
    (H : ∀W' : A.Token hh → Matrix ι ι K, ∃N,∀n,N ≤ n →
      MatrixTests.chunkSum (A.normal hh) W' (A.letters (A.next_large hh) K) n=0) :
    ∃N,∀n,N ≤ n → MatrixTests.letterSum W (A.letters hh K) n=0 := by
  let f : Codec.Raw h → Matrix ι ι (A.Algebra K h hh) := fun a=>MatrixTests.tensor (W a) (A.letters hh K a)
  let B := fragmentBound (2^h)
  let ps := (CutReduction.candidates (Codec.Raw h) B).filter (Cuts.NoCut (Codec.rawCut (A.height_pos hh)))
  let ss := (CutReduction.candidates (Codec.Raw h) B).filter (Cuts.Interval (Codec.rawCut (A.height_pos hh)))
  let token : A.Token hh → List (Codec.Raw h) := Subtype.val
  let len : A.Token hh → ℕ := fun t=>(A.normal hh t).length
  let W' : A.Token hh → Matrix ι ι K := fun t=>(t.val.map W).prod
  obtain ⟨N,hN⟩ := H W'
  let E : Matrix ι ι (A.Algebra K (D*h) (A.next_large hh)) →ₐ[K] Matrix ι ι (A.Algebra K h hh) :=
    (A.embeddingHom K hh).mapMatrix
  have ht : ∀t, E (MatrixTests.tensor (W' t) (DirectCancellation.eval (A.letters (A.next_large hh) K) (A.normal hh t))) =
      CutReduction.eval f (token t) := by
    intro t
    change _=(t.val.map (fun a=>MatrixTests.tensor (W a) (A.letters hh K a))).prod
    rw [MatrixTests.eval_tensor,A.eval_letters,A.eval_letters]
    ext i j
    change A.embeddingHom K hh (W' t i j • (A.table (D*h) (A.next_large hh)).word (FreeMonoid.ofList (A.normal hh t)))=_
    rw [map_smul,←A.normal_word]
    rfl
  have hchunk : ∀m,N ≤ m → CutReduction.chunkSum len (fun t=>CutReduction.eval f (token t)) m=0 := by
    intro m hm
    have he := congrArg E (hN m hm)
    rw [map_zero] at he
    change E (CutReduction.chunkSum len (fun t=>MatrixTests.tensor (W' t) (DirectCancellation.eval (A.letters (A.next_large hh) K) (A.normal hh t))) m)=0 at he
    simpa only [CutReduction.chunkSum,CutReduction.eval,map_sum,map_list_prod,List.map_map,Function.comp_def,ht] using he
  have hcover : ∀w,2*B+1 ≤ w.length → CutReduction.eval f w≠0 →
      ∃p∈ps,∃s∈ss,∃gs : List (A.Token hh),w=p++gs.flatMap token++s := by
    intro w hwn hwe
    have hw : Codec.Survives (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) w := by
      apply Codec.surviving_of_eval_ne_zero (K:=K) w
      intro hz
      apply hwe
      change (w.map (fun a=>MatrixTests.tensor (W a) (A.letters hh K a))).prod=0
      rw [MatrixTests.eval_tensor]
      rw [show DirectCancellation.eval (A.letters hh K) w=0 from hz,MatrixTests.tensor_zero]
    obtain ⟨p,ts,s,he,hp,hs,hpB,hsB,htn,htt⟩ := hw.raw_token_decomposition (A.threshold_four.trans hh) (by omega)
    have lift : ∃gs : List (A.Token hh),gs.map token=ts := by
      clear he hw hwn hwe htn
      induction ts with
      | nil => exact ⟨[],rfl⟩
      | cons t ts ih =>
        obtain ⟨gs,rfl⟩ := ih (fun u hu=>htt u (by simp [hu]))
        exact ⟨⟨t,htt t (by simp)⟩::gs,rfl⟩
    obtain ⟨gs,hgs⟩ := lift
    refine ⟨p,Finset.mem_filter.mpr ⟨(CutReduction.mem_candidates _ _).mpr hpB,hp⟩,
      s,Finset.mem_filter.mpr ⟨(CutReduction.mem_candidates _ _).mpr hsB,hs⟩,gs,?_⟩
    rw [←hgs] at he
    simpa only [List.flatMap] using he
  refine ⟨max (2*B+1) (2*B+(2*(2^h)+1)*N),fun n hn=>?_⟩
  exact CutReduction.eventually_letterSum_zero (Codec.rawCut (A.height_pos hh)) token
    Subtype.val_injective (fun t=>Codec.rawToken_interval (A.threshold_four.trans hh) t.property)
    ps ss (fun _ hp=>(Finset.mem_filter.mp hp).2) (fun _ hs=>(Finset.mem_filter.mp hs).2) B
    (fun _ hp=>(CutReduction.mem_candidates _ _).mp (Finset.mem_filter.mp hp).1)
    (fun _ hs=>(CutReduction.mem_candidates _ _).mp (Finset.mem_filter.mp hs).1)
    len (fun t=>(A.normal_spec hh t).1) (2*(2^h)+1) (by omega)
    (fun t=>(A.normal_spec hh t).2.2.1) f (2*B+1) N hcover hchunk n hn
end
end SourceBurnside.SourceMachine.MachineHierarchy
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type*) [CommRing K]

def LetterVanish (d : ℕ) : Prop :=
  ∀(ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ d →
    ∀W : Codec.Raw h → Matrix ι ι K, ∃N,∀n,N ≤ n → MatrixTests.letterSum W (A.letters hh K) n=0
def ChunkVanish (d b : ℕ) : Prop :=
  ∀(ι Γ : Type) [Fintype ι] [DecidableEq ι] [Fintype Γ], Fintype.card ι ≤ d →
    ∀(label : Γ → List (Codec.Raw h)),(∀c,label c≠[]) → (∀c,(label c).length ≤ b) →
    ∀W : Γ → Matrix ι ι K,∃N,∀n,N ≤ n → MatrixTests.chunkSum label W (A.letters hh K) n=0
lemma cut_step {d : ℕ} (H : A.ChunkVanish (A.next_large hh) K d 10) : A.LetterVanish hh K d := by
  intro ι _ _ hid W
  apply A.cut_reduction hh K W
  intro W'
  exact H ι (A.Token hh) hid (A.normal hh)
    (fun t=>List.ne_nil_of_length_pos (A.normal_spec hh t).1)
    (fun t=>(A.normal_spec hh t).2.1) W'
lemma automaton_step {d b : ℕ} (hb : 0<b)
    (H : A.LetterVanish hh K (b*(Fintype.card (Codec.Raw h))^b*d)) : A.ChunkVanish hh K d b := by
  intro ι Γ _ _ _ hid label hne hl W
  let : DecidableEq (Codec.Raw h) := Classical.decEq _
  let V := Automaton.blockTransition (b:=b) (Automaton.combinedWeight label W)
  have hcard : Fintype.card (Automaton.State (Codec.Raw h) b × ι) ≤ b*(Fintype.card (Codec.Raw h))^b*d := by
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul (Automaton.card_state b) hid
  obtain ⟨N,hN⟩ := H (Automaton.State (Codec.Raw h) b × ι) hcard V
  refine ⟨N,fun n hn=>?_⟩
  ext i j
  rw [←MatrixTests.automaton_block hb label hne hl W (A.letters hh K) n i j]
  change MatrixTests.letterSum V (A.letters hh K) n _ _=0
  rw [hN n hn]
  rfl
lemma direct_step [CharP K 2] {d b : ℕ} (hb : 100*b*(d^2+3)<2^h) : A.ChunkVanish hh K d b := by
  intro ι Γ _ _ _ hid label hne hl W
  refine ⟨2*fragmentBound (2^h)+1,?_⟩
  apply MatrixTests.direct_vanish_finite label hne hl (Codec.fields (A.height_pos hh)) Codec.eligibleFields (A.letters hh K)
  · exact Codec.letter_commute (A.threshold_four.trans hh)
  · exact Codec.letter_square (A.threshold_four.trans hh)
  · exact Codec.long_eligible_interval (A.threshold_four.trans hh)
  · exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.pow_le_pow_left hid 2) 3)) hb

theorem all_letter_tests [CharP K 2] (hDbig : 10*(10000+1)*(10+1)<D) (d : ℕ) :
    A.LetterVanish hh K d := by
  let H := D*h
  let size : ℕ → ℕ := fun n=>Fintype.card (Codec.Raw (HierarchyGrowth.height H D n))
  let dim : ℕ → ℕ := HierarchyGrowth.dimension (max 1 d) 10 size
  have hH : 1 ≤ H := Nat.mul_pos (by omega) (A.height_pos hh)
  have hs (n : ℕ) : size n ≤ 2^(10000*HierarchyGrowth.height H D n) := by
    simp [size,Codec.Raw,Fintype.card_fin]
  have hsize (n : ℕ) : 1 ≤ size n := Fintype.card_pos
  have hdim (n : ℕ) : 1 ≤ dim n := by
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      change 1 ≤ 10*(size n)^10*dim n
      have hs : 0 < (size n)^10 := Nat.pow_pos (hsize n)
      nlinarith
  have hlarge (n : ℕ) : A.threshold ≤ HierarchyGrowth.height H D n := by
    have hn : 1 ≤ D^n := Nat.one_le_pow n D (by omega)
    have hh' := A.next_large hh
    change A.threshold ≤ H*D^n
    exact hh'.trans (Nat.le_mul_of_pos_right H hn)
  obtain ⟨N,hN⟩ := HierarchyGrowth.stopping_index H D (max 1 d) 10 10000 size hH hDbig hs
  have hlast : A.ChunkVanish (hlarge N) K (dim N) 10 := by
    apply A.direct_step (hlarge N) K
    have hd := hdim N
    change 400*10*(dim N)^2 < 2^HierarchyGrowth.height H D N at hN
    nlinarith [Nat.one_le_iff_ne_zero.mpr (by omega : dim N≠0)]
  have hstep (i : ℕ) (Hup : A.ChunkVanish (hlarge (i+1)) K (dim (i+1)) 10) :
      A.ChunkVanish (hlarge i) K (dim i) 10 := by
    apply A.automaton_step (hlarge i) K (by decide : 0<10)
    apply A.cut_step (hlarge i) K
    simpa only [HierarchyGrowth.height_succ,dim,HierarchyGrowth.dimension,size] using Hup
  have hfirst : A.ChunkVanish (hlarge 0) K (dim 0) 10 := by
    exact Nat.decreasingInduction (motive := fun i _ => A.ChunkVanish (hlarge i) K (dim i) 10) (fun i _ hi' => hstep i hi') hlast (Nat.zero_le N)
  have hlower : A.LetterVanish hh K (max 1 d) := by
    apply A.cut_step hh K
    simpa only [HierarchyGrowth.height,pow_zero,mul_one,dim,HierarchyGrowth.dimension,H] using hfirst
  intro ι _ _ hi W
  exact hlower ι (hi.trans (le_max_right _ _)) W
theorem all_chunk_tests [CharP K 2] (hDbig : 10*(10000+1)*(10+1)<D) (d b : ℕ) (hb : 0<b) :
    A.ChunkVanish hh K d b :=
  A.automaton_step hh K hb (A.all_letter_tests hh K hDbig _)
end
end SourceBurnside.SourceMachine.MachineHierarchy

namespace SourceBurnside

structure Root (n : ℕ) where
  row : Fin n
  col : Fin n
  ne : row ≠ col
  deriving DecidableEq

abbrev Generator (n : ℕ) (R : Type u) := Root n × R

def bracket {G : Type u} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

def letter {n : ℕ} {R : Type u} (p : Root n) (a : R) :
    FreeGroup (Generator n R) := FreeGroup.of (p, a)

inductive SteinbergRel (n : ℕ) (R : Type u) [Ring R] :
    FreeGroup (Generator n R) → Prop
  | add (p : Root n) (a b : R) :
      SteinbergRel n R (letter p (a + b) * (letter p a * letter p b)⁻¹)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col) (a b : R) :
      SteinbergRel n R (bracket (letter p a) (letter q b))
  | mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      SteinbergRel n R
        (bracket (letter ⟨i, j, hij⟩ a) (letter ⟨j, k, hjk⟩ b) *
          (letter ⟨i, k, hik⟩ (a * b))⁻¹)

def Steinberg (n : ℕ) (R : Type u) [Ring R] :=
  PresentedGroup {r | SteinbergRel n R r}
  deriving Group

def Periodic (G : Type u) [Group G] : Prop := ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1

def MainStatement : Prop :=
  ∃ (R : Type) (_ : Ring R) (_ : Algebra (ZMod 2) R),
    Infinite (Steinberg 12 R) ∧ Group.IsFinitelyPresented (Steinberg 12 R) ∧
      Periodic (Steinberg 12 R)

def BurnsideStatement : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.IsFinitelyPresented G ∧ Periodic G

end SourceBurnside

namespace SourceBurnside

@[simp] theorem map_bracket {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (bracket a b) = bracket (f a) (f b) := by
  simp [bracket]

theorem bracket_eq_one_iff {G : Type u} [Group G] (a b : G) :
    bracket a b = 1 ↔ Commute a b := by
  simp only [bracket, mul_inv_eq_iff_eq_mul, one_mul]
  rfl

namespace Steinberg

variable {n : ℕ} {R : Type u} [Ring R]

def x (p : Root n) (a : R) : Steinberg n R := PresentedGroup.of (p, a)

@[simp] theorem x_add (p : Root n) (a b : R) : x p (a + b) = x p a * x p b := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (SteinbergRel.add p a b)

@[simp] theorem x_zero (p : Root n) : x p (0 : R) = 1 := by
  have h := x_add p (0 : R) 0
  simp only [zero_add] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

@[simp] theorem x_neg (p : Root n) (a : R) : x p (-a) = (x p a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← x_add, add_neg_cancel, x_zero]

theorem x_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : Commute (x p a) (x q b) := by
  apply (bracket_eq_one_iff _ _).mp
  have h := PresentedGroup.one_of_mem (SteinbergRel.commute p q h₁ h₂ a b)
  simp only [bracket, map_mul] at h
  exact h

theorem x_mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    bracket (x ⟨i, j, hij⟩ a) (x ⟨j, k, hjk⟩ b) = x ⟨i, k, hik⟩ (a * b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (SteinbergRel.mul i j k hij hjk hik a b)
  simp only [bracket, map_mul] at h
  exact h

def lift {G : Type v} [Group G] (f : Root n → R → G)
    (ha : ∀ p a b, f p (a + b) = f p a * f p b)
    (hc : ∀ p q, p.col ≠ q.row → p.row ≠ q.col → ∀ a b, Commute (f p a) (f q b))
    (hm : ∀ i j k hij hjk hik a b,
      bracket (f ⟨i, j, hij⟩ a) (f ⟨j, k, hjk⟩ b) = f ⟨i, k, hik⟩ (a * b)) :
    Steinberg n R →* G :=
  PresentedGroup.toGroup (f := fun g => f g.1 g.2) (by
    intro r hr
    cases hr with
    | add p a b => simp [letter, ha]
    | commute p q h₁ h₂ a b =>
      simpa [letter] using (bracket_eq_one_iff _ _).mpr (hc p q h₁ h₂ a b)
    | mul i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_bracket, letter, FreeGroup.lift_apply_of]
      rw [hm i j k hij hjk hik a b, mul_inv_cancel])

@[simp] theorem lift_x {G : Type v} [Group G] (f : Root n → R → G) ha hc hm
    (p : Root n) (a : R) : lift f ha hc hm (x p a) = f p a :=
  PresentedGroup.toGroup.of _

@[ext] theorem hom_ext {G : Type v} [Group G] {f g : Steinberg n R →* G}
    (h : ∀ p a, f (x p a) = g (x p a)) : f = g := by
  apply PresentedGroup.ext
  rintro ⟨p, a⟩
  exact h p a

theorem closure_range_x : Subgroup.closure (Set.range (fun g : Generator n R => x g.1 g.2)) = ⊤ :=
  PresentedGroup.closure_range_of _

def map {S : Type v} [Ring S] (f : R →+* S) : Steinberg n R →* Steinberg n S :=
  lift (fun p a => x p (f a)) (by simp) (by intros; apply x_commute <;> assumption)
    (by intros; simpa using x_mul _ _ _ _ _ _ _ _)

@[simp] theorem map_x {S : Type v} [Ring S] (f : R →+* S) (p : Root n) (a : R) :
    map f (x p a) = x p (f a) := lift_x _ _ _ _ _ _

end Steinberg

theorem burnside_of_main (h : MainStatement) : BurnsideStatement := by
  obtain ⟨R, ring, alg, hI, hF, hP⟩ := h
  exact ⟨Steinberg 12 R, inferInstance, hI, hF, hP⟩

end SourceBurnside

namespace SourceBurnside

namespace Elementary

variable {n : ℕ} {R : Type u} [Ring R]

def e (p : Root n) (a : R) : (Matrix (Fin n) (Fin n) R)ˣ where
  val := 1 + Matrix.single p.row p.col a
  inv := 1 + Matrix.single p.row p.col (-a)
  val_inv := by simp [add_mul, mul_add, p.ne.symm, ← Matrix.single_neg, add_assoc]
  inv_val := by simp [add_mul, mul_add, p.ne.symm, ← Matrix.single_neg, add_assoc]

@[simp] theorem coe_e (p : Root n) (a : R) :
    ↑(e p a) = 1 + Matrix.single p.row p.col a := rfl

@[simp] theorem e_add (p : Root n) (a b : R) : e p (a + b) = e p a * e p b := by
  apply Units.ext
  simp [coe_e, add_mul, mul_add, p.ne.symm, Matrix.single_add, add_assoc]

@[simp] theorem e_zero (p : Root n) : e p (0 : R) = 1 := by
  apply Units.ext
  simp

@[simp] theorem e_inv (p : Root n) (a : R) : (e p a)⁻¹ = e p (-a) := by
  apply Units.ext
  rfl

theorem e_commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
    (a b : R) : Commute (e p a) (e q b) := by
  change e p a * e q b = e q b * e p a
  apply Units.ext
  simp only [Units.val_mul, coe_e, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ h₁,
    Matrix.single_mul_single_of_ne _ _ _ _ h₂.symm]
  abel

theorem e_mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    bracket (e ⟨i, j, hij⟩ a) (e ⟨j, k, hjk⟩ b) = e ⟨i, k, hik⟩ (a * b) := by
  apply Units.ext
  simp only [bracket, e_inv, Units.val_mul, coe_e]
  simp only [add_mul, mul_add, one_mul, mul_one]
  simp [hij.symm, hjk.symm, hik.symm, ← Matrix.single_neg]
  abel

def representation : Steinberg n R →* (Matrix (Fin n) (Fin n) R)ˣ :=
  Steinberg.lift e e_add e_commute e_mul

@[simp] theorem representation_x (p : Root n) (a : R) :
    representation (Steinberg.x p a) = e p a := Steinberg.lift_x _ _ _ _ _ _

theorem e_injective (p : Root n) : Function.Injective (e p : R → _) := by
  intro a b h
  have h' := congrArg (fun g : (Matrix (Fin n) (Fin n) R)ˣ => g.val p.row p.col) h
  simpa [coe_e, p.ne] using h'

theorem x_injective (p : Root n) : Function.Injective (Steinberg.x p : R → _) := by
  intro a b h
  apply e_injective p
  simpa using congrArg representation h

theorem steinberg_infinite [Infinite R] (p : Root n) : Infinite (Steinberg n R) :=
  Infinite.of_injective _ (x_injective p)

end Elementary

end SourceBurnside

end

end OAI
