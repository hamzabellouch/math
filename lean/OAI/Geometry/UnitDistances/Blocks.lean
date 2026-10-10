import OAI.Geometry.UnitDistances.SmallHeight

namespace OAI

namespace PlanarUnitDistances.GenericGrid
open Filter Finset PowerGrowth
open UnitDistances.GridCount UnitDistances.GenericDiagonal

variable {ι : Type*} {F : Filter ι} (t : ι → ℝ)
variable {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

noncomputable def edges (E : ∀ i, A i → B i → Prop) (i : ι) : Finset (A i × B i) := by
  classical
  exact univ.filter fun ab => E i ab.1 ab.2

lemma edges_card_le (E : ∀ i, A i → B i → Prop) (i : ι) :
    ((edges E i).card : ℝ) ≤ (Fintype.card (A i) : ℝ) * Fintype.card (B i) := by
  classical
  have h : (edges E i).card ≤ Fintype.card (A i) * Fintype.card (B i) := by
    simpa [edges] using (Finset.card_filter_le (univ : Finset (A i × B i)) (fun ab => E i ab.1 ab.2))
  exact_mod_cast h

lemma side_card_lower (E : ∀ i, A i → B i → Prop) (ht : Tendsto t F atTop)
    (hA : Upper F t (fun i => Fintype.card (A i)) 1)
    (hB : Upper F t (fun i => Fintype.card (B i)) 1)
    (he : Lower F t (fun i => (edges E i).card) 2) :
    Lower F t (fun i => Fintype.card (A i)) 1 ∧
      Lower F t (fun i => Fintype.card (B i)) 1 := by
  have hpos : ∀ᶠ i in F, 0 < (Fintype.card (A i) : ℝ) ∧ 0 < (Fintype.card (B i) : ℝ) := by
    filter_upwards [he.eventually_pos ht] with i hi
    have hp := hi.trans_le (edges_card_le E i)
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (A i)),
      Nat.cast_nonneg (α := ℝ) (Fintype.card (B i))]
  constructor
  · have hh := he.div hB (hpos.mono fun _ h => h.2) ht
    have hm : (fun i => ((edges E i).card : ℝ) / Fintype.card (B i)) ≤ᶠ[F]
        (fun i => (Fintype.card (A i) : ℝ)) := by
      filter_upwards [hpos] with i hi
      exact (div_le_iff₀ hi.2).mpr (edges_card_le E i)
    simpa only [show (2:ℝ)-1=1 by norm_num] using hh.mono hm
  · have hh := he.div hA (hpos.mono fun _ h => h.1) ht
    have hm : (fun i => ((edges E i).card : ℝ) / Fintype.card (A i)) ≤ᶠ[F]
        (fun i => (Fintype.card (B i) : ℝ)) := by
      filter_upwards [hpos] with i hi
      exact (div_le_iff₀ hi.1).mpr (by simpa [mul_comm] using edges_card_le E i)
    simpa only [show (2:ℝ)-1=1 by norm_num] using hh.mono hm

theorem grid_card_lower (E : ∀ i, A i → B i → Prop) (ht : Tendsto t F atTop)
    (hA : Upper F t (fun i => Fintype.card (A i)) 1)
    (hB : Upper F t (fun i => Fintype.card (B i)) 1)
    (he : Lower F t (fun i => (edges E i).card) 2) (N j : ℕ) :
    Lower F t (fun i => by classical exact ((grids (E i) N j).card : ℝ)) (N+j) := by
  classical
  obtain ⟨hA', hB'⟩ := side_card_lower t E ht hA hB he
  have hposA := hA'.eventually_pos ht
  have hposB := hB'.eventually_pos ht
  have hden := hA.mul hB (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hp : ∀ᶠ i in F, 0 < (Fintype.card (A i) : ℝ) * Fintype.card (B i) := by
    filter_upwards [hposA, hposB] with i ha hb
    exact mul_pos ha hb
  have hd := he.div hden hp ht
  have hcount := ((hA'.pow ht N).mul (hB'.pow ht j) ht).mul (hd.pow ht (N*j)) ht
  simp only [one_mul, show (2:ℝ)-(1+1)=0 by norm_num, zero_mul, add_zero] at hcount
  apply hcount.mono
  filter_upwards [hposA, hposB] with i ha hb
  have : Nonempty (A i) := Fintype.card_pos_iff.mp (by exact_mod_cast ha)
  have : Nonempty (B i) := Fintype.card_pos_iff.mp (by exact_mod_cast hb)
  exact complete_grid_count (E i) N j

theorem eventually_exists_avoiding {C : ι → Type*} [∀ i, DecidableEq (C i)]
    {τ : Type*} (G : ∀ i, Finset (C i)) (bad : ∀ i, τ → Finset (C i))
    {a : ℝ} (ht : Tendsto t F atTop)
    (hG : Lower F t (fun i => (G i).card) a)
    (hb : ∀ s, Saving F t (fun i => (bad i s).card) a) (S : Finset τ) :
    ∀ᶠ i in F, ∃ x ∈ G i, ∀ s ∈ S, x ∉ bad i s := by
  have hsum := Saving.finset_sum S (fun s i => ((bad i s).card : ℝ)) (fun s _ => hb s) ht
  have hlt := hsum.eventually_lt hG ht
  filter_upwards [hlt] with i hi
  apply exists_avoiding (G i) S (bad i)
  exact_mod_cast hi

theorem choose_countable {C : ℕ → Type*} [∀ i, Nonempty (C i)] [∀ i, DecidableEq (C i)]
    {τ : Type*} [Countable τ] (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (t : ℕ → ℝ) (G : ∀ i, Finset (C i)) (bad : ∀ i, τ → Finset (C i))
    {a : ℝ} (ht : Tendsto t (U : Filter ℕ) atTop)
    (hG : Lower (U : Filter ℕ) t (fun i => (G i).card) a)
    (hb : ∀ s, Saving (U : Filter ℕ) t (fun i => (bad i s).card) a) :
    ∃ x : ∀ i, C i, (∀ᶠ i in U, x i ∈ G i) ∧ ∀ s, ∀ᶠ i in U, x i ∉ bad i s := by
  exact diagonal_countable U hU (fun i x => x ∈ G i) (fun i s x => x ∉ bad i s)
    (fun S => eventually_exists_avoiding t G bad ht hG hb S)
end PlanarUnitDistances.GenericGrid

namespace UnitDistanceBlockAvoidance
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {F σ τ : Type*} [Field F]

lemma coeff_sumAlgEquiv (p : MvPolynomial (σ ⊕ τ) F)
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    ((sumAlgEquiv F σ τ p).coeff a).coeff b = p.coeff (a.sumElim b) := by
  simp [sumAlgEquiv, AddMonoidAlgebra.curryAlgEquiv,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]

lemma coeff_degree_le (p : MvPolynomial (σ ⊕ τ) F) (a : σ →₀ ℕ) :
    ((sumAlgEquiv F σ τ p).coeff a).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro b hb
  have h : a.sumElim b ∈ p.support := by
    rw [mem_support_iff] at hb ⊢
    rwa [← coeff_sumAlgEquiv]
  have hd := le_totalDegree h
  rw [Finsupp.sum_sumElim] at hd
  exact (Nat.le_add_left _ _).trans hd

lemma outer_degree_le (p : MvPolynomial (σ ⊕ τ) F) :
    (sumAlgEquiv F σ τ p).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro a ha
  rw [mem_support_iff] at ha
  obtain ⟨b, hb⟩ : ∃ b, ((sumAlgEquiv F σ τ p).coeff a).coeff b ≠ 0 := by
    by_contra! h
    apply ha
    ext b
    simpa using h b
  have h : a.sumElim b ∈ p.support := by
    rwa [mem_support_iff, ← coeff_sumAlgEquiv]
  have hd := le_totalDegree h
  rw [Finsupp.sum_sumElim] at hd
  exact (Nat.le_add_right _ _).trans hd

lemma map_degree_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    (map f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree]
  exact Finset.sup_le fun a ha => le_totalDegree (support_map_subset f p ha)

lemma eval_blocks (p : MvPolynomial (σ ⊕ τ) F) (x : σ → F) (y : τ → F) :
    eval x (map (eval₂Hom (RingHom.id F) y) (sumAlgEquiv F σ τ p)) =
      eval (Sum.elim x y) p := by
  have h : ((aeval x).comp (mapAlgHom (aeval y))).comp
      (sumAlgEquiv F σ τ).toAlgHom = aeval (Sum.elim x y) := by
    ext i
    cases i <;> simp
  exact DFunLike.congr_fun h p

theorem two_block_zero_count {A B : Type*} [Fintype A] [Fintype B]
    (x : A → σ → F) (y : B → τ → F) (D a b : ℕ)
    (hx : ∀ q : MvPolynomial σ F, q ≠ 0 → q.totalDegree ≤ D →
      (Finset.univ.filter fun i => eval (x i) q = 0).card ≤ a)
    (hy : ∀ q : MvPolynomial τ F, q ≠ 0 → q.totalDegree ≤ D →
      (Finset.univ.filter fun j => eval (y j) q = 0).card ≤ b)
    (p : MvPolynomial (σ ⊕ τ) F) (hp : p ≠ 0) (hd : p.totalDegree ≤ D) :
    (Finset.univ.filter fun ij : A × B => eval (Sum.elim (x ij.1) (y ij.2)) p = 0).card
      ≤ a * Fintype.card B + Fintype.card A * b := by
  classical
  let P := sumAlgEquiv F σ τ p
  have hP : P ≠ 0 := by
    intro h
    apply hp
    exact (sumAlgEquiv F σ τ).injective (h.trans (map_zero _).symm)
  obtain ⟨m, hm⟩ : ∃ m, P.coeff m ≠ 0 := by
    by_contra! h
    apply hP
    apply MvPolynomial.ext
    intro m
    simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h m
  let q := P.coeff m
  have hq : (Finset.univ.filter fun j => eval (y j) q = 0).card ≤ b :=
    hy q hm ((coeff_degree_le p m).trans hd)
  have hslice (j : B) :
      (Finset.univ.filter fun i => eval (Sum.elim (x i) (y j)) p = 0).card ≤
        a + if eval (y j) q = 0 then Fintype.card A else 0 := by
    by_cases hj : eval (y j) q = 0
    · simp only [hj, ↓reduceIte]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    · simp only [hj, ↓reduceIte, add_zero]
      let r := map (eval₂Hom (RingHom.id F) (y j)) P
      have hr : r ≠ 0 := by
        intro hr
        apply hj
        have hc := congrArg (fun polynomial => polynomial.coeff m) hr
        simp only [r, coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
        exact hc
      have hrd : r.totalDegree ≤ D :=
        (map_degree_le _ P).trans ((outer_degree_le p).trans hd)
      simpa only [← eval_blocks, P, r] using hx r hr hrd
  calc
    _ = ∑ j : B, (Finset.univ.filter fun i =>
        eval (Sum.elim (x i) (y j)) p = 0).card := by
      simp only [Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ ≤ ∑ j : B, (a + if eval (y j) q = 0 then Fintype.card A else 0) :=
      Finset.sum_le_sum fun j _ => hslice j
    _ = a * Fintype.card B + Fintype.card A *
        (Finset.univ.filter fun j => eval (y j) q = 0).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.card_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
      simp only [Nat.cast_id, mul_comm]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _

universe u

abbrev BlockVars (σ : Type u) : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => BlockVars σ n ⊕ σ

abbrev BlockTuples (A : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => BlockTuples A n × A

instance blockTuplesFintype (A : Type*) [Fintype A] (n : ℕ) :
    Fintype (BlockTuples A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd (BlockTuples A n) A ih inferInstance

lemma blockTuples_card (A : Type*) [Fintype A] (n : ℕ) :
    Fintype.card (BlockTuples A n) = Fintype.card A ^ n := by
  induction n with
  | zero =>
    let : Unique (BlockTuples A 0) := inferInstanceAs (Unique PUnit)
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (BlockTuples A n × A) = _
    rw [Fintype.card_prod, ih, pow_succ]

def blockEval {A : Type*} (x : A → σ → F) :
    (n : ℕ) → BlockTuples A n → BlockVars σ n → F
  | 0, _ => PEmpty.elim
  | n + 1, u => Sum.elim (blockEval x n u.1) (x u.2)

def zeroCap (m a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => zeroCap m a n * m + m ^ n * a

lemma zeroCap_succ (m a n : ℕ) : zeroCap m a (n + 1) = (n + 1) * a * m ^ n := by
  induction n with
  | zero => simp [zeroCap]
  | succ n ih => rw [zeroCap, ih, pow_succ]; ring

theorem blocks_zero_count {A : Type*} [Fintype A]
    (x : A → σ → F) (D a : ℕ)
    (hx : ∀ q : MvPolynomial σ F, q ≠ 0 → q.totalDegree ≤ D →
      (Finset.univ.filter fun i => eval (x i) q = 0).card ≤ a)
    (n : ℕ) (p : MvPolynomial (BlockVars σ n) F)
    (hp : p ≠ 0) (hd : p.totalDegree ≤ D) :
    (Finset.univ.filter fun u => eval (blockEval x n u) p = 0).card ≤
      zeroCap (Fintype.card A) a n := by
  classical
  induction n with
  | zero =>
    let : IsEmpty (BlockVars σ 0) := inferInstanceAs (IsEmpty PEmpty)
    have hne (u : BlockTuples A 0) : eval (blockEval x 0 u) p ≠ 0 := by
      obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (BlockVars σ 0) p
      simpa only [eval_C, ne_eq, C_eq_zero] using hp
    have hz : (Finset.univ.filter fun u => eval (blockEval x 0 u) p = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hne u (Finset.mem_filter.mp hu).2
    rw [hz]; exact Nat.zero_le _
  | succ n ih =>
    have h := two_block_zero_count (blockEval x n) x D
      (zeroCap (Fintype.card A) a n) a (fun q hq hqd => ih q hq hqd) hx p hp hd
    have he : (Finset.univ.filter fun u : BlockTuples A (n+1) =>
        eval (blockEval x (n+1) u) p = 0) =
        (Finset.univ.filter fun ij : BlockTuples A n × A =>
          eval (Sum.elim (blockEval x n ij.1) (x ij.2)) p = 0) := by
      apply Finset.ext
      intro u
      constructor <;> intro hu
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    rw [he]
    simpa only [zeroCap, blockTuples_card] using h

end UnitDistanceBlockAvoidance

namespace UnitDistanceBlockAvoidance
open MvPolynomial
open scoped BigOperators
variable {K A σ : Type*} [Field K] [Fintype A]

noncomputable def zeroSet (x : A → σ → K) (p : MvPolynomial σ K) : Finset A := by
  classical
  exact Finset.univ.filter fun i => eval (x i) p = 0

noncomputable def maxZeros (x : A → σ → K) (D : ℕ) : ℕ :=
  sSup {m | ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = m}

lemma attainable_zeros_nonempty (x : A → σ → K) (D : ℕ) :
    {m | ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = m}.Nonempty := by
  refine ⟨0, 1, one_ne_zero, ?_, ?_⟩
  · simp
  · simp [zeroSet]

lemma attainable_zeros_bdd (x : A → σ → K) (D : ℕ) :
    BddAbove {m | ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = m} := by
  refine ⟨Fintype.card A, ?_⟩
  rintro m ⟨p, _, _, rfl⟩
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma zeroSet_card_le (x : A → σ → K) (D : ℕ) (p : MvPolynomial σ K)
    (hp : p ≠ 0) (hd : p.totalDegree ≤ D) : (zeroSet x p).card ≤ maxZeros x D :=
  le_csSup (attainable_zeros_bdd x D) ⟨p, hp, hd, rfl⟩

lemma maxZeros_attained (x : A → σ → K) (D : ℕ) :
    ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = maxZeros x D :=
  Nat.sSup_mem (attainable_zeros_nonempty x D) (attainable_zeros_bdd x D)

lemma maxZeros_le (x : A → σ → K) (D : ℕ) (b : ℝ)
    (h : ∀ p : MvPolynomial σ K, p ≠ 0 → p.totalDegree ≤ D → ((zeroSet x p).card : ℝ) ≤ b) :
    (maxZeros x D : ℝ) ≤ b := by
  obtain ⟨p, hp, hd, he⟩ := maxZeros_attained x D
  simpa [he] using h p hp hd

def tupleEquiv (A : Type*) : (n : ℕ) → BlockTuples A n ≃ (Fin n → A)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := fun u => by cases u; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n+1 => (Equiv.prodCongr (tupleEquiv A n) (Equiv.refl A)).trans
      ((Equiv.prodComm _ _).trans (Fin.consEquiv fun _ : Fin (n+1) => A))

noncomputable def blockGrids {B : Type*} [Fintype B] (E : A → B → Prop) (N j : ℕ) :
    Finset (BlockTuples A N × BlockTuples B j) := by
  classical
  exact (UnitDistances.GridCount.grids E N j).map
    (Equiv.prodCongr (tupleEquiv A N) (tupleEquiv B j)).symm.toEmbedding

lemma blockGrids_card {B : Type*} [Fintype B] (E : A → B → Prop) (N j : ℕ) :
    (blockGrids E N j).card = by classical exact (UnitDistances.GridCount.grids E N j).card := by
  classical
  exact Finset.card_map _

lemma mem_blockGrids {B : Type*} [Fintype B] (E : A → B → Prop) (N j : ℕ)
    (u : BlockTuples A N × BlockTuples B j) : u ∈ blockGrids E N j ↔
      ∀ i l, E (tupleEquiv A N u.1 i) (tupleEquiv B j u.2 l) := by
  classical
  simp [blockGrids, UnitDistances.GridCount.grids]
end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance
variable {ι : Type*} {F : Filter ι} {t : ι → ℝ}
variable {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable {K σ τ : Type*} [Field K]

def UniformBlocks (F : Filter ι) (t : ι → ℝ) {A : ι → Type*} [∀ i, Fintype (A i)]
    (x : ∀ i, A i → σ → K) : Prop :=
  ∀ D, Saving F t (fun i => maxZeros (x i) D) 1

lemma zeroCap_upper (x : ∀ i, A i → σ → K) (D n : ℕ) {b : ℝ}
    (hcard : Upper F t (fun i => Fintype.card (A i)) 1)
    (hx : Upper F t (fun i => maxZeros (x i) D) b) (ht : Tendsto t F atTop) :
    Upper F t (fun i => (zeroCap (Fintype.card (A i)) (maxZeros (x i) D) (n+1) : ℝ))
      (b+n) := by
  have hm := hx.mul (hcard.pow (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht n)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => pow_nonneg (Nat.cast_nonneg _) _) ht
  have hh := hm.const_mul ht (show (0:ℝ) ≤ n+1 by positivity)
  simp only [one_mul] at hh
  apply hh.congr
  exact Eventually.of_forall fun i => by simp [zeroCap_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_assoc]

theorem polynomial_test_saving (x : ∀ i, A i → σ → K) (y : ∀ i, B i → τ → K)
    (hA : Upper F t (fun i => Fintype.card (A i)) 1)
    (hB : Upper F t (fun i => Fintype.card (B i)) 1)
    (hx : UniformBlocks F t x) (hy : UniformBlocks F t y) (ht : Tendsto t F atTop)
    (N j : ℕ)
    (p : ι → MvPolynomial (BlockVars σ (N+1) ⊕ BlockVars τ (j+1)) K)
    (D : ℕ) (hp : ∀ᶠ i in F, p i ≠ 0 ∧ (p i).totalDegree ≤ D) :
    Saving F t (fun i => (zeroSet (fun u : BlockTuples (A i) (N+1) × BlockTuples (B i) (j+1) =>
      Sum.elim (blockEval (x i) (N+1) u.1) (blockEval (y i) (j+1) u.2)) (p i)).card)
      ((N+1:ℕ)+(j+1:ℕ)) := by
  obtain ⟨b, hb, hx⟩ := hx D
  obtain ⟨c, hc, hy⟩ := hy D
  have hu := (zeroCap_upper x D N hA hx ht).mul
    (hB.pow (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht (j+1))
    (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => pow_nonneg (Nat.cast_nonneg _) _) ht
  have hv := (hA.pow (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht (N+1)).mul
    (zeroCap_upper y D j hB hy ht)
    (Eventually.of_forall fun _ => pow_nonneg (Nat.cast_nonneg _) _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hs₁ : Saving F t
      (fun i => (zeroCap (Fintype.card (A i)) (maxZeros (x i) D) (N+1) : ℝ) *
        (Fintype.card (B i) : ℝ)^(j+1)) ((N+1:ℕ)+(j+1:ℕ)) := by
    refine ⟨_, ?_, hu⟩
    push_cast
    linarith
  have hs₂ : Saving F t
      (fun i => (Fintype.card (A i) : ℝ)^(N+1) *
        (zeroCap (Fintype.card (B i)) (maxZeros (y i) D) (j+1) : ℝ))
      ((N+1:ℕ)+(j+1:ℕ)) := by
    refine ⟨_, ?_, hv⟩
    push_cast
    linarith
  obtain ⟨e, he, hh⟩ := hs₁.add hs₂ ht
  refine ⟨e, he, hh.mono ?_⟩
  filter_upwards [hp] with i hi
  have h := two_block_zero_count (blockEval (x i) (N+1)) (blockEval (y i) (j+1)) D
    (zeroCap (Fintype.card (A i)) (maxZeros (x i) D) (N+1))
    (zeroCap (Fintype.card (B i)) (maxZeros (y i) D) (j+1))
    (fun q hq hd => blocks_zero_count (x i) D (maxZeros (x i) D)
      (fun r hr hrd => zeroSet_card_le (x i) D r hr hrd) (N+1) q hq hd)
    (fun q hq hd => blocks_zero_count (y i) D (maxZeros (y i) D)
      (fun r hr hrd => zeroSet_card_le (y i) D r hr hrd) (j+1) q hq hd)
    (p i) hi.1 hi.2
  have haCard : Fintype.card (BlockTuples (A i) (N+1)) = Fintype.card (A i) ^ (N+1) :=
    (Fintype.card_congr (tupleEquiv (A i) (N+1))).trans (by simp)
  have hbCard : Fintype.card (BlockTuples (B i) (j+1)) = Fintype.card (B i) ^ (j+1) :=
    (Fintype.card_congr (tupleEquiv (B i) (j+1))).trans (by simp)
  rw [haCard, hbCard] at h
  exact_mod_cast h
end PlanarUnitDistances.GenericGrid

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance
variable {K σ τ : Type*} [Field K]
variable {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]

def optionalCoordinates (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K) (N j n : ℕ)
    (u : Option (BlockTuples (A n) N × BlockTuples (B n) j)) :
    (BlockVars σ N ⊕ BlockVars τ j) → K :=
  u.elim (fun _ => 0) (fun v => Sum.elim (blockEval (x n) N v.1) (blockEval (y n) j v.2))

theorem choose_polynomial_tests {T : Type*} [Countable T]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (t : ℕ → ℝ)
    (ht : Tendsto t (U : Filter ℕ) atTop)
    (E : ∀ n, A n → B n → Prop)
    (hA : Upper (U : Filter ℕ) t (fun n => Fintype.card (A n)) 1)
    (hB : Upper (U : Filter ℕ) t (fun n => Fintype.card (B n)) 1)
    (he : Lower (U : Filter ℕ) t (fun n => (edges E n).card) 2)
    (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K)
    (hx : UniformBlocks (U : Filter ℕ) t x) (hy : UniformBlocks (U : Filter ℕ) t y)
    (N j : ℕ) (p : T → ℕ → MvPolynomial (BlockVars σ (N+1) ⊕ BlockVars τ (j+1)) K)
    (hp : ∀ s, ∃ D : ℕ, ∀ᶠ n in U, p s n ≠ 0 ∧ (p s n).totalDegree ≤ D) :
    ∃ u : ∀ n, Option (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)),
      (∀ᶠ n in U, ∃ v, u n = some v ∧ v ∈ blockGrids (E n) (N+1) (j+1)) ∧
      ∀ s, ∀ᶠ n in U, eval (optionalCoordinates x y (N+1) (j+1) n (u n)) (p s n) ≠ 0 := by
  classical
  let emb (n : ℕ) : (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)) ↪
      Option (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)) :=
    ⟨some, Option.some_injective _⟩
  let G n := (blockGrids (E n) (N+1) (j+1)).map (emb n)
  let bad n s := (zeroSet (fun v : BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1) =>
      Sum.elim (blockEval (x n) (N+1) v.1) (blockEval (y n) (j+1) v.2)) (p s n)).map (emb n)
  have hG : Lower (U : Filter ℕ) t (fun n => (G n).card) ((N+1:ℕ)+(j+1:ℕ)) := by
    apply (grid_card_lower t E ht hA hB he (N+1) (j+1)).congr
    exact Eventually.of_forall fun n => by
      simp only [G, Finset.card_map]
      exact_mod_cast (blockGrids_card (E n) (N+1) (j+1)).symm
  have hb : ∀ s, Saving (U : Filter ℕ) t (fun n => (bad n s).card) ((N+1:ℕ)+(j+1:ℕ)) := by
    intro s
    obtain ⟨D, hD⟩ := hp s
    obtain ⟨e, he, h⟩ := polynomial_test_saving x y hA hB hx hy ht N j (p s) D hD
    refine ⟨e, he, h.congr ?_⟩
    exact Eventually.of_forall fun n => by simp [bad]
  obtain ⟨u, hu, hs⟩ := choose_countable U hU t G bad ht hG hb
  have hgood : ∀ᶠ n in U, ∃ v, u n = some v ∧ v ∈ blockGrids (E n) (N+1) (j+1) := by
    filter_upwards [hu] with n hn
    obtain ⟨v, hv, hvu⟩ := Finset.mem_map.mp hn
    exact ⟨v, hvu.symm, hv⟩
  refine ⟨u, hgood, ?_⟩
  intro s
  filter_upwards [hgood, hs s] with n hn hns
  obtain ⟨v, hvu, hv⟩ := hn
  rw [hvu]
  intro hzero
  apply hns
  apply Finset.mem_map.mpr
  refine ⟨v, ?_, hvu.symm⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
end PlanarUnitDistances.GenericGrid

namespace UnitDistances.UltraField
open Filter MvPolynomial
variable {ι σ : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i, Field (K i)]

lemma mvmap_zero_iff (p : MvPolynomial σ (∀ i, K i)) :
    MvPolynomial.map (mk U K) p = 0 ↔
      ∀ᶠ i in U, MvPolynomial.map (Pi.evalRingHom K i) p = 0 := by
  classical
  constructor
  · intro hz
    have hc (m : σ →₀ ℕ) : ∀ᶠ i in U, p.coeff m i = 0 := by
      apply (mk_eq_zero U K _).mp
      simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        using congrArg (fun polynomial => polynomial.coeff m) hz
    filter_upwards [(eventually_all_finset p.support).mpr (fun m _ => hc m)] with i hi
    ext m
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases hm : m ∈ p.support
    · exact hi m hm
    · rw [notMem_support_iff.mp hm]
      rfl
  · intro hz
    ext m
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mk_eq_zero]
    filter_upwards [hz] with i hi
    simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Pi.evalRingHom_apply]
      using congrArg (fun polynomial => polynomial.coeff m) hi

lemma mvmap_eventually_ne_zero (p : MvPolynomial σ (∀ i, K i))
    (hp : MvPolynomial.map (mk U K) p ≠ 0) :
    ∀ᶠ i in U, MvPolynomial.map (Pi.evalRingHom K i) p ≠ 0 :=
  Ultrafilter.eventually_not.mpr ((mvmap_zero_iff U K p).not.mp hp)

lemma mvmap_totalDegree_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (p : MvPolynomial σ R) :
    (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree := by
  classical
  apply Finset.sup_mono
  exact MvPolynomial.support_map_subset _ _

lemma mvmap_eval (p : MvPolynomial σ (∀ i, K i)) (x : σ → ∀ i, K i) :
    eval (fun s => mk U K (x s)) (MvPolynomial.map (mk U K) p) =
      mk U K (fun i => eval (fun s => x s i) (MvPolynomial.map (Pi.evalRingHom K i) p)) := by
  rw [eval_map]
  change eval₂ (mk U K) ((mk U K) ∘ x) p = _
  rw [← MvPolynomial.eval₂_comp]
  congr 1
  funext i
  symm
  rw [eval_map]
  exact MvPolynomial.eval₂_comp (Pi.evalRingHom K i) x p |>.symm
end UnitDistances.UltraField

namespace UnitDistanceBlockAvoidance
instance blockVars_countable {σ : Type*} [Countable σ] (n : ℕ) : Countable (BlockVars σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Countable PEmpty)
  | succ n ih => exact @instCountableSum (BlockVars σ n) σ ih inferInstance
end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {K σ τ : Type*} [Field K] [Countable σ] [Countable τ]
variable {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]

theorem exists_independent_grid
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (t : ℕ → ℝ)
    (ht : Tendsto t (U : Filter ℕ) atTop)
    (E : ∀ n, A n → B n → Prop)
    (hA : Upper (U : Filter ℕ) t (fun n => Fintype.card (A n)) 1)
    (hB : Upper (U : Filter ℕ) t (fun n => Fintype.card (B n)) 1)
    (he : Lower (U : Filter ℕ) t (fun n => (edges E n).card) 2)
    (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K)
    (hx : UniformBlocks (U : Filter ℕ) t x) (hy : UniformBlocks (U : Filter ℕ) t y)
    (N j : ℕ) (L : Type*) [Field L] [Countable L]
    [Algebra L (FieldProduct U (fun _ => K))] :
    ∃ u : ∀ n, Option (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)),
      (∀ᶠ n in U, ∃ v, u n = some v ∧ v ∈ blockGrids (E n) (N+1) (j+1)) ∧
      AlgebraicIndependent L (fun s => mk U (fun _ => K)
        (fun n => optionalCoordinates x y (N+1) (j+1) n (u n) s)) := by
  classical
  let V := BlockVars σ (N+1) ⊕ BlockVars τ (j+1)
  have : Countable (MvPolynomial V L) :=
    AddMonoidAlgebra.coeff_injective.countable
  let T := {p : MvPolynomial V L // p ≠ 0}
  let φ := algebraMap L (FieldProduct U (fun _ => K))
  have lift (p : T) : ∃ q : MvPolynomial V (ℕ → K),
      MvPolynomial.map (mk U (fun _ => K)) q = MvPolynomial.map φ p.val :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective _
  choose q hq using lift
  let tests (s : T) (n : ℕ) := MvPolynomial.map (Pi.evalRingHom (fun _ => K) n) (q s)
  have hp (s : T) : ∃ D, ∀ᶠ n in U, tests s n ≠ 0 ∧ (tests s n).totalDegree ≤ D := by
    refine ⟨(q s).totalDegree, ?_⟩
    have hn : MvPolynomial.map (mk U (fun _ => K)) (q s) ≠ 0 := by
      rw [hq s]
      simpa only [map_zero] using (MvPolynomial.map_injective φ φ.injective).ne s.property
    filter_upwards [mvmap_eventually_ne_zero U (fun _ => K) (q s) hn] with n hn
    exact ⟨hn, mvmap_totalDegree_le _ _⟩
  obtain ⟨u, hu, htst⟩ := choose_polynomial_tests U hU t ht E hA hB he x y hx hy N j tests hp
  refine ⟨u, hu, algebraicIndependent_iff.mpr ?_⟩
  intro p hzero
  by_contra hp0
  let s : T := ⟨p, hp0⟩
  have heval : eval (fun v => mk U (fun _ => K)
        (fun n => optionalCoordinates x y (N+1) (j+1) n (u n) v))
      (MvPolynomial.map (mk U (fun _ => K)) (q s)) = 0 := by
    rw [hq s, eval_map]
    exact hzero
  rw [mvmap_eval] at heval
  have hz := (mk_eq_zero U (fun _ => K) _).mp heval
  have hn := htst s
  obtain ⟨n, hn0, hn1⟩ := (hz.and hn).exists
  exact hn1 hn0
end PlanarUnitDistances.GenericGrid

namespace UnitDistanceBlockAvoidance
variable {A σ F : Type*}

def varIndex (σ : Type*) : (n : ℕ) → Fin n × σ → BlockVars σ n
  | 0, ij => Fin.elim0 ij.1
  | n+1, ij => Fin.cases (Sum.inr ij.2) (fun j => Sum.inl (varIndex σ n (j,ij.2))) ij.1

lemma varIndex_injective (σ : Type*) (n : ℕ) : Function.Injective (varIndex σ n) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i.1
  | succ n ih =>
    rintro ⟨i,s⟩ ⟨j,t⟩ h
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact Prod.ext rfl (Sum.inr.inj h)
      | succ j => simp [varIndex] at h
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [varIndex] at h
      | succ j =>
        have hh : (i,s)=(j,t) := ih (Sum.inl.inj h)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
        rfl

lemma blockEval_varIndex (x : A → σ → F) (n : ℕ) (u : BlockTuples A n)
    (ij : Fin n × σ) :
    blockEval x n u (varIndex σ n ij)=x (tupleEquiv A n u ij.1) ij.2 := by
  induction n with
  | zero => exact Fin.elim0 ij.1
  | succ n ih =>
    obtain ⟨j,s⟩ := ij
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      exact ih u.1 (j,s)
end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {K σ τ L : Type*} [Field K] [Field L]
variable {A B : ℕ → Type*}

def leftCoords (x : ∀ n, A n → σ → K) (N j n : ℕ)
    (u : Option (BlockTuples (A n) N × BlockTuples (B n) j)) (is : Fin N × σ) : K :=
  match u with
  | none => 0
  | some v => x n (tupleEquiv (A n) N v.1 is.1) is.2

def rightCoords (y : ∀ n, B n → τ → K) (N j n : ℕ)
    (u : Option (BlockTuples (A n) N × BlockTuples (B n) j)) (is : Fin j × τ) : K :=
  match u with
  | none => 0
  | some v => y n (tupleEquiv (B n) j v.2 is.1) is.2

lemma independent_left_right (U : Ultrafilter ℕ)
    [Algebra L (FieldProduct U (fun _ => K))]
    (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K) (N j : ℕ)
    (u : ∀ n, Option (BlockTuples (A n) N × BlockTuples (B n) j))
    (h : AlgebraicIndependent L (fun s => mk U (fun _ => K)
      (fun n => optionalCoordinates x y N j n (u n) s))) :
    AlgebraicIndependent L (fun is => mk U (fun _ => K) (fun n => leftCoords x N j n (u n) is)) ∧
    AlgebraicIndependent L (fun is => mk U (fun _ => K) (fun n => rightCoords y N j n (u n) is)) := by
  constructor
  · convert h.comp (fun is => Sum.inl (varIndex σ N is))
      (Sum.inl_injective.comp (varIndex_injective σ N)) using 1
    funext is
    congr 1
    funext n
    cases hu : u n with
    | none => rfl
    | some v => exact (blockEval_varIndex (x n) N v.1 is).symm
  · convert h.comp (fun is => Sum.inr (varIndex τ j is))
      (Sum.inr_injective.comp (varIndex_injective τ j)) using 1
    funext is
    congr 1
    funext n
    cases hu : u n with
    | none => rfl
    | some v => exact (blockEval_varIndex (y n) j v.2 is).symm
end PlanarUnitDistances.GenericGrid

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {σ τ : Type*} [Countable σ] [Countable τ]

theorem exists_real_grid (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (t : ℕ → ℝ) (ht : Tendsto t (U : Filter ℕ) atTop)
    (A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
    (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
    (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
    (he : Lower (U : Filter ℕ) t
      (fun n => (edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
    (x : ℂ → σ → ℂ) (y : ℂ → τ → ℂ)
    (hx0 : ∀ s, x 0 s=0) (hy0 : ∀ s, y 0 s=0)
    (hx : UniformBlocks (U : Filter ℕ) t (fun n (a : A n) => x a))
    (hy : UniformBlocks (U : Filter ℕ) t (fun n (b : B n) => y b))
    (N j : ℕ) (L : Type*) [Field L] [Countable L]
    [Algebra L (FieldProduct U (fun _ => ℂ))] :
    ∃ p : Fin (N+1) → ℕ → ℂ, ∃ r : Fin (j+1) → ℕ → ℂ,
      (∀ᶠ n in U, ∀ i j, p i n ∈ A n ∧ r j n ∈ B n ∧ E n (p i n) (r j n)) ∧
      AlgebraicIndependent L (fun iq : Fin (N+1) × σ => mk U (fun _ => ℂ)
        (fun n => x (p iq.1 n) iq.2)) ∧
      AlgebraicIndependent L (fun iq : Fin (j+1) × τ => mk U (fun _ => ℂ)
        (fun n => y (r iq.1 n) iq.2)) := by
  classical
  obtain ⟨u,hu,hai⟩ := exists_independent_grid U hU t ht
    (fun n (a : A n) (b : B n) => E n a b)
    (by simpa only [Fintype.card_coe] using hA)
    (by simpa only [Fintype.card_coe] using hB) he
    (fun n (a : A n) => x a) (fun n (b : B n) => y b) hx hy N j L
  let p : Fin (N+1) → ℕ → ℂ := fun i n => match u n with
    | none => 0
    | some v => (tupleEquiv (A n) (N+1) v.1 i).val
  let r : Fin (j+1) → ℕ → ℂ := fun i n => match u n with
    | none => 0
    | some v => (tupleEquiv (B n) (j+1) v.2 i).val
  refine ⟨p,r,?_,?_,?_⟩
  · filter_upwards [hu] with n hn
    obtain ⟨v,hv,he⟩ := hn
    intro i q
    refine ⟨?_,?_,?_⟩
    · simpa only [p,hv] using (tupleEquiv (A n) (N+1) v.1 i).property
    · simpa only [r,hv] using (tupleEquiv (B n) (j+1) v.2 q).property
    · simpa only [p,r,hv] using (mem_blockGrids _ _ _ v).mp he i q
  · have hh := (independent_left_right U _ _ _ _ u hai).1
    convert hh using 1
    funext iq
    congr 1
    funext n
    cases hv : u n with
    | none => simpa only [p,hv,leftCoords] using hx0 iq.2
    | some v => simp only [p,hv,leftCoords]
  · have hh := (independent_left_right U _ _ _ _ u hai).2
    convert hh using 1
    funext iq
    congr 1
    funext n
    cases hv : u n with
    | none => simpa only [r,hv,rightCoords] using hy0 iq.2
    | some v => simp only [r,hv,rightCoords]
end PlanarUnitDistances.GenericGrid

end OAI
