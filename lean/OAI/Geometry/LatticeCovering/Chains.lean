import OAI.Geometry.LatticeCovering.Lines

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


def concat {m b : ℕ} (P : (Fin b → Bool) → Finset (Fin m → ℝ))
    (lam : Fin b → ℝ) : Finset (Fin (m+b) → ℝ) := by
  classical
  exact (join P (bits b lam)).image (fun x => Fin.append x.1 x.2)

lemma append_injective {m b : ℕ} :
    Function.Injective (fun x : (Fin m → ℝ) × (Fin b → ℝ) => Fin.append x.1 x.2) := by
  intro x y h
  apply Prod.ext
  · funext j
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd b j)
  · funext j
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd m j)

lemma mem_concat {m b : ℕ} (P : (Fin b → Bool) → Finset (Fin m → ℝ))
    (lam : Fin b → ℝ) (x : Fin (m+b) → ℝ) :
    x ∈ concat P lam ↔ ∃ e, ∃ v ∈ P e, x=Fin.append v (bits b lam e) := by
  classical
  rw [concat, Finset.mem_image]
  constructor
  · rintro ⟨⟨v,w⟩,hvw,rfl⟩
    obtain ⟨e,he,hwe⟩ := (mem_join P (bits b lam) (v,w)).mp hvw
    exact ⟨e,v,he,by rw [hwe]⟩
  · rintro ⟨e,v,hv,rfl⟩
    exact ⟨(v,bits b lam e),(mem_join _ _ _).mpr ⟨e,hv,rfl⟩,rfl⟩

lemma suffixBinary_subset {m : ℕ} {P Q : Finset (Fin m → ℝ)}
    (hP : SuffixBinary P) (hQ : Q ⊆ P) : SuffixBinary Q := by
  intro j y
  obtain ⟨a,ha⟩ := hP j y
  exact ⟨a,fun x hx => ha x (hQ hx)⟩




theorem suffixBinary_concat {m b : ℕ}
    (P : (Fin b → Bool) → Finset (Fin m → ℝ)) (lam : Fin b → ℝ)
    (hP : ∀ e, SuffixBinary (P e)) : SuffixBinary (concat P lam) := by
  classical
  intro j y
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · by_cases hn : ∃ e : Fin b → Bool, bits b lam e = (fun k => y (Fin.natAdd m k))
    · obtain ⟨e,he⟩ := hn
      obtain ⟨a,ha⟩ := hP e j (fun k => y (Fin.castAdd b k))
      refine ⟨a,?_⟩
      intro x hx hxy
      obtain ⟨e',v,hv,rfl⟩ := (mem_concat P lam x).mp hx
      have he' : bits b lam e' = bits b lam e := by
        funext k
        rw [he]
        simpa only [Fin.append_right] using hxy (Fin.natAdd m k) (by
          change j.val < m+k.val
          omega)
      have heq : e'=e := bits_injective b lam he'
      subst e'
      simpa only [Fin.append_left] using ha v hv (fun k hk => by
        simpa only [Fin.append_left] using hxy (Fin.castAdd b k) (by
          exact hk))
    · refine ⟨0,?_⟩
      intro x hx hxy
      obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam x).mp hx
      apply False.elim
      apply hn
      refine ⟨e,?_⟩
      funext k
      simpa only [Fin.append_right] using hxy (Fin.natAdd m k) (by
        change j.val < m+k.val
        omega)
  · refine ⟨lam j,?_⟩
    intro x hx hxy
    obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam x).mp hx
    simpa only [Fin.append_right] using bits_scalar b lam e j


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators


structure Block where
  b : ℕ
  p : ℕ
  prime : p.Prime
  h : ℝ
  h_pos : 0 < h
  usable : Finset (Fin b → ZMod p)
  direction : Fin b → ZMod p
  direction_ne : direction ≠ 0

namespace Block
abbrev Group (B : Block) := Fin B.b → ZMod B.p
abbrev Vec (B : Block) := Fin B.b → ℝ
instance (B : Block) : Fact B.p.Prime := ⟨B.prime⟩

def lattice (B : Block) : Submodule ℤ B.Vec :=
  codeLattice B.p (Submodule.span (ZMod B.p) {B.direction})

def g (B : Block) : B.Group → ℝ :=
  lineMax (K := ZMod B.p) (sparseWeight (K := ZMod B.p) B.usable
    (fun z => folded B.h (anchor B.p z))) B.direction

def grid (B : Block) (y : B.Vec) : B.Group :=
  residue B.p (floorVector B.p (fun j => y j/B.h))

def weight (B : Block) (y l : B.Vec) : ℝ :=
  B.h^B.b/(B.p : ℝ)*gamma (fun j => y j-B.h*l j)

def det (B : Block) : ℝ := B.h^B.b/(B.p : ℝ)

lemma g_nonneg (B : Block) (x : B.Group) : 0 ≤ B.g x :=
  lineMax_nonneg (K := ZMod B.p) (fun z => by
    unfold sparseWeight
    split_ifs
    · exact div_nonneg (folded_pos B.h_pos _).le (Nat.cast_nonneg _)
    · exact le_refl 0) _ _

lemma weight_pos (B : Block) (y l : B.Vec) : 0 < B.weight y l := by
  unfold weight gamma
  exact mul_pos (div_pos (pow_pos B.h_pos _) (by exact_mod_cast B.prime.pos))
    (Finset.prod_pos (fun j _ => gamma1_pos _))

lemma weight_bits (B : Block) (y lam : B.Vec) (e : Fin B.b → Bool) :
    B.weight y (bits B.b lam e) =
      atom B.h ((fun j => y j/B.h)-lam) e/(B.p : ℝ) := by
  have he : (fun j => y j-B.h*bits B.b lam e j) =
      (fun j => B.h*(((fun j => y j/B.h)-lam) j-bitValue (e j))) := by
    funext j
    simp only [bits, bitValue, Pi.sub_apply]
    field_simp [B.h_pos.ne']
    ring
  simp only [weight, atom, Fintype.card_fin, he]
  ring


lemma cell (B : Block) (y : B.Vec) (hg : 0 < B.g (B.grid y)) :
    ∃ z ∈ B.usable, ∃ lam : B.Vec,
      lam ∈ B.lattice ∧
      B.g (B.grid y) = folded B.h (anchor B.p z)/(B.p : ℝ) ∧
      (∀ e : Fin B.b → Bool, bits B.b lam e ∈ B.lattice ∧
        (∀ j, |y j-B.h*bits B.b lam e j| ≤ B.h) ∧
        Real.exp (-((B.b : ℝ)*B.h^2/B.p)) *
          (B.g (B.grid y)*wordMass B.h (anchor B.p z) e) ≤ B.weight y (bits B.b lam e)) := by
  obtain ⟨z,hz,lam,hlam,ht,hg',he⟩ := gaussian_cell B.h_pos B.usable B.direction
    (fun j => y j/B.h) hg
  change B.g (B.grid y) = folded B.h (anchor B.p z)/(B.p : ℝ) at hg'
  refine ⟨z,hz,lam,hlam,hg',?_⟩
  intro e
  obtain ⟨hm,hr,hw⟩ := he e
  refine ⟨hm,?_,?_⟩
  · intro j
    convert hr j using 1
    congr 1
    dsimp only [bits]
    simp only [bitValue]
    field_simp [B.h_pos.ne']
    ring
  · rw [weight_bits, hg']
    simpa only [Fintype.card_fin] using hw


def shift (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec) : A.Vec :=
  fun j => A.h/(A.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k

lemma shift_grid_bits (A B : Block) (w : Fin B.b → A.Group) (y : A.Vec)
    (lam : B.Vec) (e : Fin B.b → Bool) :
    A.grid (y-A.shift B w (bits B.b lam e)) =
      A.grid (y-A.shift B w lam)-Bits.groupShift w e := by
  ext j
  have hp : (A.p : ℝ) ≠ 0 := by exact_mod_cast A.prime.pos.ne'
  have hh : A.h ≠ 0 := A.h_pos.ne'
  have hs :
      (A.p : ℝ)*((y-A.shift B w (bits B.b lam e)) j/A.h) =
      (A.p : ℝ)*((y-A.shift B w lam) j/A.h)-
        (((∑ k, if e k then ((w k j).val : ℤ) else 0) : ℤ) : ℝ) := by
    simp only [Pi.sub_apply, shift, bits]
    rw [Int.cast_sum]
    simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero]
    have hs' : (∑ k, ((w k j).val : ℝ)*(lam k+if e k then 1 else 0)) =
        (∑ k, ((w k j).val : ℝ)*lam k) + (∑ k, if e k then ((w k j).val : ℝ) else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      cases he : e k <;> simp [mul_add]
    rw [hs']
    field_simp
    ring
  simp only [Pi.sub_apply] at hs
  simp only [grid, residue, floorVector, Pi.sub_apply]
  rw [hs, Int.floor_sub_intCast, Int.cast_sub, Int.cast_sum]
  congr 1
  simp only [Bits.groupShift, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases he : e k <;> simp



end Block
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators



inductive Chain : Block → Type
  | base (B : Block) : Chain B
  | append {A : Block} (c : Chain A) (B : Block)
      (w : Fin B.b → A.Group) : Chain B

namespace Chain
variable {A B : Block}

abbrev dim : {B : Block} → Chain B → ℕ
  | _, .base B => B.b
  | _, .append c B _ => c.dim+B.b

abbrev Vec (c : Chain B) := Fin c.dim → ℝ

def last : {B : Block} → (c : Chain B) → c.Vec → B.Vec
  | _, .base _, y => y
  | _, .append c _ _, y => fun j => y (Fin.natAdd c.dim j)

def subLast : {B : Block} → (c : Chain B) → c.Vec → B.Vec → c.Vec
  | _, .base _, y, t => y-t
  | _, .append c _ _, y, t =>
      Fin.append (fun j => y (Fin.castAdd _ j)) (fun j => y (Fin.natAdd c.dim j)-t j)

@[simp] lemma last_subLast (c : Chain B) (y : c.Vec) (t : B.Vec) :
    c.last (c.subLast y t) = c.last y-t := by
  cases c <;> simp [last, subLast, Pi.sub_def]


def RawMem : {B : Block} → (c : Chain B) → c.Vec → Prop
  | _, .base B, l => l ∈ B.lattice
  | _, .append c B _, l =>
      c.RawMem (fun j => l (Fin.castAdd B.b j)) ∧
      (fun j => l (Fin.natAdd c.dim j)) ∈ B.lattice



def weight : {B : Block} → (c : Chain B) → c.Vec → c.Vec → ℝ
  | _, .base B, y, l => B.weight y l
  | _, .append (A := A) c B w, y, l =>
      c.weight (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) *
      B.weight (fun j => y (Fin.natAdd c.dim j)) (fun j => l (Fin.natAdd c.dim j))

def Residual : {B : Block} → (c : Chain B) → c.Vec → c.Vec → Prop
  | _, .base B, y, l => ∀ j, |y j-B.h*l j| ≤ B.h
  | _, .append (A := A) c B w, y, l =>
      c.Residual (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) ∧
      ∀ j, |y (Fin.natAdd c.dim j)-B.h*l (Fin.natAdd c.dim j)| ≤ B.h



def coefficient (loss : Block → ℝ) : {B : Block} → Chain B → ℝ
  | _, .base B => Real.exp (-((B.b : ℝ)*B.h^2/B.p))
  | _, .append (A := A) c B _ =>
      c.coefficient loss * Real.exp (-((B.b : ℝ)*B.h^2/B.p)) * (1-loss B)*(1-loss A)

def Good (loss : Block → ℝ) : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B w =>
      c.Good loss ∧ 0 ≤ 1-loss B ∧ 0 ≤ 1-loss A ∧
      1-loss A ≤ (𝔼 x, A.g x) ∧
      ∀ z ∈ B.usable, ∀ x : A.Group,
        (1-loss B)*(𝔼 y, A.g y) ≤
          ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * A.g (x-Bits.groupShift w e)

lemma coefficient_nonneg (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss) :
    0 ≤ c.coefficient loss := by
  induction c with
  | base B => exact (Real.exp_pos _).le
  | append c B w ih =>
    exact mul_nonneg (mul_nonneg (mul_nonneg (ih hc.1) (Real.exp_pos _).le) hc.2.1) hc.2.2.1

lemma weight_pos (c : Chain B) (y l : c.Vec) : 0 < c.weight y l := by
  induction c with
  | base B => exact B.weight_pos y l
  | append c B w ih => exact mul_pos (ih _ _) (B.weight_pos _ _)

lemma base_pattern (B : Block) (y : B.Vec) :
    ∃ P : Finset B.Vec, SuffixBinary P ∧
      (∀ l ∈ P, l ∈ B.lattice ∧ ∀ j, |y j-B.h*l j| ≤ B.h) ∧
      Real.exp (-((B.b : ℝ)*B.h^2/B.p))*B.g (B.grid y) ≤ ∑ l ∈ P, B.weight y l := by
  classical
  by_cases hg : 0 < B.g (B.grid y)
  · obtain ⟨z,hz,lam,hlam,hmax,he⟩ := B.cell y hg
    let P : Finset B.Vec := Finset.univ.image (bits B.b lam)
    refine ⟨P,?_,?_,?_⟩
    · intro j t
      refine ⟨lam j,?_⟩
      intro l hl hlt
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hl
      exact bits_scalar B.b lam e j
    · intro l hl
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨(he e).1,(he e).2.1⟩
    · change _ ≤ ∑ l ∈ Finset.univ.image (bits B.b lam), _
      rw [Finset.sum_image (fun e he e' he' h => bits_injective B.b lam h)]
      calc
        _ = ∑ e, Real.exp (-((B.b : ℝ)*B.h^2/B.p)) *
            (B.g (B.grid y)*wordMass B.h (anchor B.p z) e) := by
          rw [←Finset.mul_sum, ←Finset.mul_sum, wordMass_sum B.h_pos, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun e _ => (he e).2.2)
  · have heq : B.g (B.grid y)=0 := le_antisymm (le_of_not_gt hg) (B.g_nonneg _)
    refine ⟨∅,?_,by simp,?_⟩
    · intro j t
      exact ⟨0,by simp⟩
    · simp [heq]




theorem truncated_patterns (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss)
    (y : c.Vec) :
    ∃ P : Finset c.Vec, SuffixBinary P ∧
      (∀ l ∈ P, c.RawMem l ∧ c.Residual y l) ∧
      c.coefficient loss*B.g (B.grid (c.last y)) ≤ ∑ l ∈ P, c.weight y l := by
  classical
  induction c with
  | base B => exact base_pattern B y
  | @append A c B w ih =>
    let yl : c.Vec := fun j => y (Fin.castAdd B.b j)
    let yr : B.Vec := fun j => y (Fin.natAdd c.dim j)
    by_cases hg : 0 < B.g (B.grid yr)
    · obtain ⟨z,hz,lam,hlam,hmax,he⟩ := B.cell yr hg
      have hcp := fun e : Fin B.b → Bool => ih hc.1 (c.subLast yl (A.shift B w (bits B.b lam e)))
      choose P hPb hPm hPw using hcp
      refine ⟨concat P lam,suffixBinary_concat P lam hPb,?_,?_⟩
      · intro l hl
        obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam l).mp hl
        have hv' := hPm e v hv
        exact ⟨by simpa [RawMem] using And.intro hv'.1 (he e).1,
          by simpa [Residual] using And.intro hv'.2 (he e).2.1⟩
      · let x := A.grid (c.last yl-A.shift B w lam)
        have hgrid (e : Fin B.b → Bool) :
            A.grid (c.last (c.subLast yl (A.shift B w (bits B.b lam e)))) =
              x-Bits.groupShift w e := by
          rw [last_subLast, Block.shift_grid_bits]
        have hs : (1-loss B)*(1-loss A) ≤
            ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * A.g (x-Bits.groupShift w e) :=
          (mul_le_mul_of_nonneg_left hc.2.2.2.1 hc.2.1).trans (hc.2.2.2.2 z hz x)
        have hw := weighted_join P (bits B.b lam) (bits_injective B.b lam)
          (fun e l => c.weight (c.subLast yl (A.shift B w (bits B.b lam e))) l)
          (fun e => B.weight yr (bits B.b lam e))
          (fun l => (Chain.append c B w).weight y (Fin.append l.1 l.2))
          (wordMass B.h (anchor B.p z)) (fun e => A.g (x-Bits.groupShift w e))
          (c.coefficient loss) (B.g (B.grid yr)) (Real.exp (-((B.b : ℝ)*B.h^2/B.p)))
          ((1-loss B)*(1-loss A)) (coefficient_nonneg c loss hc.1) (B.g_nonneg _)
          (Real.exp_pos _).le
          (fun e => Finset.prod_nonneg (fun j _ => (probability_pos B.h_pos _ _).le))
          (fun e => A.g_nonneg _)
          (fun e => by convert (he e).2.2 using 1 ; ring)
          (fun e => by rw [←hgrid e]; exact hPw e)
          (fun e l hl => by simp [weight,yl,yr]) hs
        change _ ≤ ∑ l ∈ (join P (bits B.b lam)).image (fun x => Fin.append x.1 x.2), _
        rw [Finset.sum_image (fun x hx y hy h => append_injective h)]
        convert hw using 1 ; dsimp [coefficient, last,yr] ; ring
    · have heq : B.g (B.grid yr)=0 := le_antisymm (le_of_not_gt hg) (B.g_nonneg _)
      refine ⟨∅,?_,by simp,?_⟩
      · intro j t
        exact ⟨0,by simp⟩
      · change _*B.g (B.grid yr) ≤ _
        simp [heq]


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded Blocks ConstructionA Filter Topology
open scoped BigOperators

def blockLoss (A : ℝ) (B : Block) : ℝ := A*(B.b : ℝ)^(-(1/100 : ℝ))


def Regular (A : ℝ) (B : Block) : Prop :=
  B.h = height B.b ∧
  (B.b : ℝ)*logMean (height B.b)-4*(B.b : ℝ)^(56/100 : ℝ) ≤ Real.log B.p ∧
  Real.log B.p ≤ (B.b : ℝ)*logMean (height B.b)-3*(B.b : ℝ)^(56/100 : ℝ) ∧
  B.usable ⊆ eligible B.b B.p ∧
  |(𝔼 x, B.g x)-1| ≤ blockLoss A B ∧
  (∀ x, B.g x ≤ Real.exp (5*(B.b : ℝ)^(56/100 : ℝ)))

lemma regular_mean {A : ℝ} {B : Block} (hB : Regular A B) (hsmall : blockLoss A B ≤ 1/2) :
    1/2 ≤ (𝔼 x, B.g x) ∧ (𝔼 x, B.g x) ≤ 2 := by
  have h := abs_le.mp hB.2.2.2.2.1
  constructor <;> linarith




theorem block_preparation : ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 2 ≤ N ∧
    (∀ b ≥ N, A*(b : ℝ)^(-(1/100 : ℝ)) ≤ 1/2 ∧ logMean (height b) ≤ (b : ℝ)) ∧
    (∀ b ≥ N, ∃ B : Block, B.b=b ∧ Regular A B) ∧
    (∀ (P : Block), N ≤ P.b → Regular A P → ∀ b ≥ N,
      (P.b : ℝ) ≤ (b : ℝ)^((1 : ℝ)/(9/10)) →
      ∃ B : Block, ∃ w : Fin B.b → P.Group,
        B.b=b ∧ Regular A B ∧
        ∀ z ∈ B.usable, ∀ x : P.Group,
          (1-blockLoss A B)*(𝔼 y, P.g y) ≤
            ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * P.g (x-Bits.groupShift w e)) := by
  classical
  obtain ⟨A,hA,hsel⟩ := eventually_usable_gaussian.{0}
  have hsmall : ∀ᶠ b : ℕ in atTop, A*(b : ℝ)^(-(1/100 : ℝ)) ≤ 1/2 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).const_mul A
    have hn : Tendsto (fun b : ℕ => A*(b : ℝ)^(-(1/100 : ℝ))) atTop (𝓝 0) := by
      have hcast : Tendsto (fun b : ℕ => (b : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,mul_zero] using ht.comp hcast
    exact hn.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hsel.and (eventually_height_prime.and (hsmall.and (eventually_logMean_height_le.and (eventually_ge_atTop (2 : ℕ))))))
  let N' := max N 2
  have hN' : 2 ≤ N' := le_max_right _ _
  have hbN (b : ℕ) (hb : N' ≤ b) := hN b ((le_max_left _ _).trans hb)
  refine ⟨A,hA,N',hN',?_,?_,?_⟩
  · intro b hb
    exact ⟨(hbN b hb).2.2.1,(hbN b hb).2.2.2.1⟩
  · intro b hb
    obtain ⟨p,hp,hpl,hpu⟩ := (hbN b hb).2.1
    let : Fact p.Prime := ⟨hp⟩
    have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
    obtain ⟨w,U,v,hU,hs,hM,hg,hcap⟩ := (hbN b hb).1 p hpl hpu PUnit (by simp) 1 (by norm_num)
      (Real.one_le_rpow hb1 (by norm_num)) (fun _ => 1) (by simp)
      (fun x => by simp)
      (by norm_num) (by norm_num)
    let B : Block := ⟨b,p,hp,height b,heightR_pos (by exact_mod_cast (show 1 < b by omega)),U,v,v.property⟩
    refine ⟨B,rfl,rfl,hpl,hpu,hU,?_,?_⟩
    · exact hg
    · exact fun x => (hcap x).2
  · intro P hP hPreg b hb hrel
    obtain ⟨p,hp,hpl,hpu⟩ := (hbN b hb).2.1
    let : Fact p.Prime := ⟨hp⟩
    have hb1 : 1 ≤ b := by omega
    have hP1 : 1 ≤ (P.b : ℝ) := by exact_mod_cast (show 1 ≤ P.b by omega)
    have hg := regular_mean hPreg (hbN P.b hP).2.2.1
    have hcard := group_log_bound hb1 (hbN P.b hP).2.2.2.1 hrel hPreg.2.2.1
    obtain ⟨w,U,v,hU,hs,hM,hmean,hcap⟩ := (hbN b hb).1 p hpl hpu P.Group hcard
      (P.b : ℝ) hP1 hrel P.g P.g_nonneg hPreg.2.2.2.2.2 hg.1 hg.2
    let B : Block := ⟨b,p,hp,height b,heightR_pos (by exact_mod_cast (show 1 < b by omega)),U,v,v.property⟩
    refine ⟨B,w,rfl,⟨rfl,hpl,hpu,hU,hmean,fun x => (hcap x).2⟩,?_⟩
    exact hs


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators
namespace Block

def roundingLoss (B : Block) : ℝ := (B.b : ℝ)*B.h^2/(B.p : ℝ)
lemma roundingLoss_nonneg (B : Block) : 0 ≤ B.roundingLoss := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
end Block

namespace Chain
variable {A B : Block}

def first : {B : Block} → Chain B → Block
  | _, .base B => B
  | _, .append c _ _ => c.first

def Every (P : Block → Prop) : {B : Block} → Chain B → Prop
  | _, .base B => P B
  | _, .append c B _ => c.Every P ∧ P B

lemma every_last {P : Block → Prop} (c : Chain B) (hc : c.Every P) : P B := by
  cases c with
  | base B => exact hc
  | append c B w => exact hc.2
lemma every_mono {P Q : Block → Prop} (c : Chain B) (hc : c.Every P)
    (h : ∀ B, P B → Q B) : c.Every Q := by
  induction c with
  | base B => exact h B hc
  | append c B w ih => exact ⟨ih hc.1,h B hc.2⟩

def blockSum (f : Block → ℝ) : {B : Block} → Chain B → ℝ
  | _, .base B => f B
  | _, .append c B _ => c.blockSum f+f B

lemma blockSum_nonneg (c : Chain B) (f : Block → ℝ) (hf : c.Every (fun B => 0 ≤ f B)) :
    0 ≤ c.blockSum f := by
  induction c with
  | base B => exact hf
  | append c B w ih => exact add_nonneg (ih hf.1) hf.2
lemma blockSum_le (c : Chain B) (f g : Block → ℝ) (h : c.Every (fun B => f B ≤ g B)) :
    c.blockSum f ≤ c.blockSum g := by
  induction c with
  | base B => exact h
  | append c B w ih => exact add_le_add (ih h.1) h.2
lemma blockSum_mul (c : Chain B) (a : ℝ) (f : Block → ℝ) :
    c.blockSum (fun B => a*f B) = a*c.blockSum f := by
  induction c with
  | base B => rfl
  | append c B w ih => simp only [blockSum,ih,mul_add]

def Halving : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B _ => c.Halving ∧ 2*B.b ≤ A.b


theorem inverse_power_sum (c : Chain B) (a : ℝ) (ha : 0 < a)
    (hc : c.Halving) (hpos : c.Every (fun B => 0 < B.b)) :
    c.blockSum (fun B => (B.b : ℝ)^(-a)) ≤ (B.b : ℝ)^(-a)/(1-(2 : ℝ)^(-a)) := by
  have hq0 : 0 ≤ (2 : ℝ)^(-a) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : (2 : ℝ)^(-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ha)
  have hd : 0 < 1-(2 : ℝ)^(-a) := sub_pos.mpr hq1
  induction c with
  | base B =>
    change (B.b : ℝ)^(-a) ≤ (B.b : ℝ)^(-a)/(1-(2 : ℝ)^(-a))
    apply (le_div_iff₀ hd).mpr
    have hu := Real.rpow_nonneg (Nat.cast_nonneg B.b) (-a)
    nlinarith
  | @append A c B w ih =>
    have hi := ih hc.1 hpos.1
    have hp : (0 : ℝ) < B.b := by exact_mod_cast hpos.2
    have hh : (2 : ℝ)*B.b ≤ A.b := by exact_mod_cast hc.2
    have he : (A.b : ℝ)^(-a) ≤ (2 : ℝ)^(-a)*(B.b : ℝ)^(-a) := by
      have ht := Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) hp) hh (neg_nonpos.mpr ha.le)
      rwa [Real.mul_rpow (by norm_num) hp.le] at ht
    change c.blockSum (fun B => (B.b : ℝ)^(-a))+(B.b : ℝ)^(-a) ≤ _
    have hi' := (le_div_iff₀ hd).mp hi
    apply (le_div_iff₀ hd).mpr
    nlinarith

lemma mul_deficit {x y : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) :
    1-x*y ≤ (1-x)+(1-y) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]



theorem coefficient_bounds (c : Chain B) (loss : Block → ℝ)
    (hl : c.Every (fun B => loss B ∈ Set.Icc 0 1)) :
    0 ≤ c.coefficient loss ∧ c.coefficient loss ≤ 1 ∧
      1-c.coefficient loss+loss B ≤ c.blockSum (fun B => B.roundingLoss+2*loss B) := by
  have he (B : Block) : 0 ≤ Real.exp (-B.roundingLoss) ∧
      Real.exp (-B.roundingLoss) ≤ 1 ∧ 1-Real.exp (-B.roundingLoss) ≤ B.roundingLoss := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr B.roundingLoss_nonneg),?_⟩
    have h := Real.add_one_le_exp (-B.roundingLoss)
    linarith
  induction c with
  | base B =>
    change 0 ≤ Real.exp (-B.roundingLoss) ∧ Real.exp (-B.roundingLoss) ≤ 1 ∧ _
    refine ⟨(he B).1,(he B).2.1,?_⟩
    change 1-Real.exp (-B.roundingLoss)+loss B ≤ B.roundingLoss+2*loss B
    linarith [(he B).2.2,hl.1]
  | @append A c B w ih =>
    obtain ⟨hc0,hc1,hcd⟩ := ih hl.1
    have hA := c.every_last hl.1
    have hB := hl.2
    have hx0 : 0 ≤ c.coefficient loss*Real.exp (-B.roundingLoss) := mul_nonneg hc0 (he B).1
    have hx1 : c.coefficient loss*Real.exp (-B.roundingLoss) ≤ 1 :=
      (mul_le_mul hc1 (he B).2.1 (he B).1 (by norm_num)).trans_eq (by ring)
    have hy0 : 0 ≤ c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B) :=
      mul_nonneg hx0 (sub_nonneg.mpr hB.2)
    have hy1 : c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B) ≤ 1 :=
      (mul_le_mul hx1 (by linarith [hB.1] : 1-loss B ≤ 1) (sub_nonneg.mpr hB.2) (by norm_num)).trans_eq (by ring)
    change 0 ≤ c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B)*(1-loss A) ∧ _
    refine ⟨mul_nonneg hy0 (sub_nonneg.mpr hA.2),?_,?_⟩
    · exact (mul_le_mul hy1 (by linarith [hA.1] : 1-loss A ≤ 1) (sub_nonneg.mpr hA.2) (by norm_num)).trans_eq (by ring)
    · have hd1 := mul_deficit hc1 (he B).2.1
      have hd2 := mul_deficit hx1 (show 1-loss B ≤ 1 by linarith [hB.1])
      have hd3 := mul_deficit hy1 (show 1-loss A ≤ 1 by linarith [hA.1])
      change 1-c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B)*(1-loss A)+loss B ≤
        c.blockSum (fun B => B.roundingLoss+2*loss B)+(B.roundingLoss+2*loss B)
      linarith [(he B).2.2]



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks Filter Topology
open scoped BigOperators


def nextSize (b : ℕ) : ℕ := ⌈(b : ℝ)^(9/10 : ℝ)⌉₊

lemma nextSize_relation (b : ℕ) : (b : ℝ) ≤ (nextSize b : ℝ)^((1 : ℝ)/(9/10)) := by
  have hn : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have he := Real.rpow_le_rpow (Real.rpow_nonneg hn _) (Nat.le_ceil ((b : ℝ)^(9/10 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 1/(9/10))
  rw [←Real.rpow_mul hn] at he
  norm_num at he
  simpa [nextSize] using he

lemma eventually_nextSize_half : ∀ᶠ b : ℕ in atTop, 2*nextSize b ≤ b := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_rpow_ratio_bound (by norm_num : (9/10 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/4)), eventually_ge_atTop (4 : ℕ)] with b hb hb4
  have hb4' : (4 : ℝ) ≤ b := by exact_mod_cast hb4
  have hc : (nextSize b : ℝ) < (b : ℝ)^(9/10 : ℝ)+1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg b) (9/10 : ℝ))
  have hp : (b : ℝ)^(9/10 : ℝ) ≤ (b : ℝ)/4 := by
    simpa only [Real.rpow_one,div_eq_mul_inv,mul_comm,one_mul] using hb
  have hn : (2 : ℝ)*(nextSize b : ℝ) ≤ b := by
    linarith only [hc,hp,hb4']
  exact_mod_cast hn

namespace Chain
variable {B : Block}
def CeilingSizes : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B _ => c.CeilingSizes ∧ B.b=nextSize A.b
end Chain



theorem hierarchy_preparation : ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 2 ≤ N ∧
    (∀ b ≥ N, A*(b : ℝ)^(-(1/100 : ℝ)) ≤ 1/2 ∧ logMean (height b) ≤ (b : ℝ)) ∧
    ∀ cutoff ≥ N, ∀ b₁ ≥ cutoff,
      ∃ B : Block, ∃ c : Chain B,
        c.first.b=b₁ ∧ c.Every (fun B => cutoff ≤ B.b ∧ Regular A B) ∧
        c.Good (blockLoss A) ∧ c.Halving ∧ c.CeilingSizes ∧ nextSize B.b < cutoff := by
  classical
  obtain ⟨A,hA,N,hN,hsmall,hfirst,hnext⟩ := block_preparation
  obtain ⟨M,hM⟩ := eventually_atTop.mp eventually_nextSize_half
  let N' := max N M
  have hNN : N ≤ N' := le_max_left _ _
  have hMN : M ≤ N' := le_max_right _ _
  refine ⟨A,hA,N',hN.trans hNN,fun b hb => hsmall b (hNN.trans hb),?_⟩
  intro cutoff hcut b₁ hb₁
  have hcutN : N ≤ cutoff := hNN.trans hcut
  have hext : ∀ b : ℕ, ∀ P : Block, P.b=b → ∀ c : Chain P,
      c.Every (fun B => cutoff ≤ B.b ∧ Regular A B) →
      c.Good (blockLoss A) → c.Halving → c.CeilingSizes →
      ∃ B : Block, ∃ d : Chain B,
        d.first=c.first ∧ d.Every (fun B => cutoff ≤ B.b ∧ Regular A B) ∧
        d.Good (blockLoss A) ∧ d.Halving ∧ d.CeilingSizes ∧ nextSize B.b < cutoff := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro P hPb c hc hg hh hs
      have hP := c.every_last hc
      by_cases hstop : nextSize P.b < cutoff
      · exact ⟨P,c,rfl,hc,hg,hh,hs,hstop⟩
      · have hgo : cutoff ≤ nextSize P.b := le_of_not_gt hstop
        have hhalf : 2*nextSize P.b ≤ P.b := hM P.b (hMN.trans (hcut.trans hP.1))
        have hlt : nextSize P.b < b := by
          have hP2 : 2 ≤ P.b := hN.trans (hcutN.trans hP.1)
          omega
        obtain ⟨Q,w,hQb,hQ,hws⟩ := hnext P (hcutN.trans hP.1) hP.2
          (nextSize P.b) (hcutN.trans hgo) (nextSize_relation P.b)
        have hQcut : cutoff ≤ Q.b := hQb ▸ hgo
        have hc' : (Chain.append c Q w).Every (fun B => cutoff ≤ B.b ∧ Regular A B) :=
          ⟨hc,hQcut,hQ⟩
        have hsmP : blockLoss A P ≤ 1/2 := (hsmall P.b (hcutN.trans hP.1)).1
        have hsmQ : blockLoss A Q ≤ 1/2 := (hsmall Q.b (hcutN.trans hQcut)).1
        have hmean : 1-blockLoss A P ≤ (𝔼 x, P.g x) := by
          have ht := (abs_le.mp hP.2.2.2.2.2.1).1
          linarith
        have hg' : (Chain.append c Q w).Good (blockLoss A) :=
          ⟨hg,by linarith,by linarith,hmean,hws⟩
        have hh' : (Chain.append c Q w).Halving := ⟨hh,by rwa [hQb]⟩
        have hs' : (Chain.append c Q w).CeilingSizes := ⟨hs,hQb⟩
        obtain ⟨R,d,hdf,hdc,hdg,hdh,hds,hdt⟩ := ih (nextSize P.b) hlt Q hQb
          (Chain.append c Q w) hc' hg' hh' hs'
        exact ⟨R,d,hdf,hdc,hdg,hdh,hds,hdt⟩
  obtain ⟨P,hPb,hP⟩ := hfirst b₁ (hcutN.trans hb₁)
  have hPc : cutoff ≤ P.b := hPb ▸ hb₁
  obtain ⟨B,c,hcf,hc,hg,hh,hs,ht⟩ := hext P.b P rfl (Chain.base P)
    ⟨hPc,hP⟩ trivial trivial trivial
  refine ⟨B,c,?_,hc,hg,hh,hs,ht⟩
  rw [hcf]
  exact hPb


end SingleLatticeCovering.Vertical

noncomputable section
open Module MeasureTheory

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
