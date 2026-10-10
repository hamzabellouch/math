import OAI.Combinatorics.HadwigerCounterexample.QuadraticTesters
import OAI.Combinatorics.HadwigerCounterexample.KeyDirections
import OAI.Combinatorics.HadwigerCounterexample.SumRankBounds

namespace OAI

/-! # Atom Flavors -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Finset Function
open scoped BigOperators
variable {g r n b : ℕ} {p : Shape}

abbrev Flavor (g : ℕ) := Option (Option (Finset (Tag g × Tag g)))
namespace Flavor
abbrev full {g : ℕ} : Flavor g := none
abbrev sharedOnly {g : ℕ} : Flavor g := some none
abbrev pure {g : ℕ} (s : Finset (Tag g × Tag g)) : Flavor g := some (some s)

def keeps (f : Flavor g) (x : Tag g) (y : Block g) : Prop :=
  match f,y with
  | none, .inl (i,_) => allowed i x
  | some none,.inl _ => False
  | some (some s),.inl (i,j) => allowed i x ∧ (i,j) ∈ s
  | some (some _), .inr v => v≠0
  | _, .inr _ => True
instance (f : Flavor g) (x : Tag g) (y : Block g) : Decidable (keeps f x y) :=
  Classical.propDecidable _

theorem keep_o {f : Flavor g} {x : Tag g} {i j}
    (h : keeps f x (Block.O i j)) : allowed i x := by
  rcases f with (_|_|_) <;> simp [keeps] at h
  · exact h
  exact h.1

theorem keepZ (f : Flavor g) (x : Tag g) : keeps f x Block.Z := by
  rcases f with (_|_|_) <;> simp [keeps]
theorem keepSharp (f : Flavor g) (x : Tag g) : keeps f x Block.sharp := by
  rcases f with (_|_|_) <;> simp [keeps]

end Flavor

abbrev Knobs (g n : ℕ) := Block g → Vec (Fin n)

def lit (f : Flavor g) (x : Tag g) (y : Knobs g n) : Base g n :=
  fun i => if f.keeps x i.1 then y i.1 i.2 else 0

theorem lit_allows (f : Flavor g) (x : Tag g) (y : Knobs g n) :
    allows x (lit f x y) :=
  fun _ _ h _ => ite_eq_right (fun g => h (Flavor.keep_o g))

def useAtom (p : Shape) {n : ℕ} (x : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) := atom p x s (lit f x y)
theorem mem_useAtom (p : Shape) {n : ℕ} (x : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (y : Knobs p.g n) : useAtom p x s f y∈Xspace p n :=
  atom_mem s (lit_allows f x y)

abbrev ProbeIdx (g : ℕ) := (Tag g × Tag g)⊕Unit
abbrev Digest (g : ℕ) := Vec (ProbeIdx g)

def asBlock (i : ProbeIdx g) : Block g := i.elim (fun q => Block.O q.1 q.2) (fun _ => Block.S)
theorem asBlock_inj {g : ℕ} : Injective (@asBlock g) := by
  rintro (⟨i,j⟩|⟨⟩) (⟨k,l⟩|⟨⟩) e <;> simp_all [asBlock,Block.O,Block.S]

def zget (y : Vec (Fin n)) (i : ℕ) := if h:i<n then y ⟨i,h⟩ else 0
def tested (r : ℕ) (y : Vec (Fin n)) :=
  ∑ i : Fin r,zget y (2*i.val)*zget y (2*i.val+1)

def scan (p : Shape) {n} (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :
    Digest p.g :=
  fun i => if Flavor.keeps f l (asBlock i) then tested p.r (x (asBlock i)) else 0

namespace Digest
variable (q : Digest g)

def feasible (l : Tag g) (f : Flavor g) := ∀ i,¬ Flavor.keeps f l (asBlock i) → q i=0

def diagO := ∑ d : Tag g, ∑ t,q (.inl (d,t))
def sumBit := q.diagO+q (.inr ())

end Digest

theorem scan_feasible (p : Shape) {n} (l) (f : Flavor p.g) (x : Knobs p.g n) :
    (scan p l f x).feasible l f := fun _ h => ite_eq_right h

theorem scan_is (p : Shape) {n} (l) (s : Label p.b) (f : Flavor p.g) (x : Knobs p.g n)
    (i : ProbeIdx p.g) :
    scan p l f x i=etab p n (asBlock i) (mom p s (lit f l x)) := by
  classical
  rw [mom,etab_point]
  let d := asBlock i
  unfold scan
  split
  · rename_i he
    have hg j : readBit (lit f l x) d j=zget (x d) j := by
      by_cases h : j<n <;> simp [readBit,zget,h,lit,d,he]
    unfold tested test
    simp_rw [show ∀ j, readBit (lit f l x) (asBlock i) j=zget (x (asBlock i)) j from hg]
  rename_i he
  unfold test
  have hZ j :
      readBit (lit f l x) (asBlock i) j=0 := by
    by_cases h : j<n <;> simp [readBit,lit,h,he]
  simp_rw [hZ,zero_mul,Finset.sum_const_zero]

theorem etaScan (p : Shape) {n} (l s f) (x : Knobs p.g n) :
    (scan p l f x).sumBit=eta p n (mom p s (lit f l x)) := by
  simp only [Digest.sumBit,Digest.diagO,eta,etaO,LinearMap.add_apply,LinearMap.sum_apply]
  simp_rw [scan_is p l s]
  rfl

theorem role_scan (p : Shape) {n} (l s f) (x : Knobs p.g n) :
    role p n (useAtom p l s f x)=(scan p l f x).diagO := by
  unfold Digest.diagO useAtom atom
  let M := mom p s (lit f l x)
  have h (i : Tag p.g) :
      (Pi.single l M : Tag p.g → Moment p n) i∈Wtag p n i := by
    by_cases h : i=l
    · subst i; rw [Pi.single_eq_same]
      exact Submodule.subset_span ⟨_,_,lit_allows f l x,rfl⟩
    simp [h]
  rw [role_cut _ _ h,Finset.sum_eq_single l]
  · rw [Pi.single_eq_same,etaO,LinearMap.sum_apply]
    simp_rw [LinearMap.sum_apply,scan_is p l s]
    rfl
  · intro i _ hi; simp [hi]
  simp

def dialed (p : Shape) {n} (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :=
  (scan p l f x).sumBit

def spins (p : Shape) (n : ℕ) : Wgt (Knobs p.g n) := draws (Block p.g) unif

theorem spins_law (p : Shape) (n : ℕ) : IsLaw (spins p n) := draws_law unif_law

/-- Projection notation for conditioning on a specified (possible)
diagnostic or diagonal only. -/
def scopedBit (p : Shape) (n : ℕ) (l : Tag p.g) (f : Flavor p.g) (q : F) :
    Wgt (Knobs p.g n) := onW (spins p n) (fun x => dialed p l f x=q)
def scopedScan (p : Shape) (n : ℕ) (l : Tag p.g) (f : Flavor p.g) (z : Digest p.g) :
    Wgt (Knobs p.g n) := onW (spins p n) (fun x => scan p l f x=z)

end HadwigerCounterexample

end

end OAI
