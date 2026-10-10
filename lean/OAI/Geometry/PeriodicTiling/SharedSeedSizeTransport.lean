import OAI.Geometry.PeriodicTiling.SharedSeedInverse

namespace OAI

universe uK uΔ uA uB uR

noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} {A : Type uA} {B : Type uB} {R : Type uR}
  [AddCommGroup K] [AddCommGroup R] {a b m n : ℕ}

def usefulOneOfEq (ha : a = 2) (D : LabeledBlocks K A B a b)
    (u : K) (s : LabelledResidue m) : ZMod a × ZMod b := by
  subst a
  exact usefulOne D u s

def highOneOfEq (ha : a = 2) (D : LabeledBlocks K A B a b)
    (t : ℤ) (u : K) (s : LabelledResidue m) : K := by
  subst a
  exact highOne D t u s

def usefulTwoOfEq (ha : a = 3) (D : LabeledBlocks K A B a b)
    (u : K) (s : LabelledResidue m) : ZMod a × ZMod b := by
  subst a
  exact usefulTwo D u s

def highTwoOfEq (ha : a = 3) (D : LabeledBlocks K A B a b)
    (t : ℤ) (u : K) (s : LabelledResidue m) : K := by
  subst a
  exact highTwo D t u s

def oneForwardOfEq (ha : a = 2) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod a × ZMod b) × K) × ZMod n :=
  ((usefulOneOfEq ha D (k - v.1.1) (e (sx - v.2)) + S.e v.1.2,
    highOneOfEq ha D (x - H v) (k - v.1.1) (e (sx - v.2))),
    sharedOutput e code (x - H v) (sx - v.2))

def twoForwardOfEq (ha : a = 3) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod a × ZMod b) × K) × ZMod n :=
  ((usefulTwoOfEq ha D (k - v.1.1) (e (sx - v.2)) + S.e v.1.2,
    highTwoOfEq ha D (x - H v) (k - v.1.1) (e (sx - v.2))),
    sharedOutput e code (x - H v) (sx - v.2))

theorem oneForwardOfEq_bijective
    (ha : a = 2) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod a) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 3) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (oneForwardOfEq ha D S e code H x sx k) := by
  subst a
  exact oneForward_bijective D S e code H hA hB hOther x sx k

theorem twoForwardOfEq_bijective
    (ha : a = 3) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod a) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 2) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (twoForwardOfEq ha D S e code H x sx k) := by
  subst a
  exact twoForward_bijective D S e code H hA hB hOther x sx k

theorem usefulOneOfEq_active
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 2) (D : LabeledBlocks K A B a b)
    (u : K) {s : LabelledResidue m} (hs : ActiveOne s) : usefulOneOfEq ha D u s = D.C u := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · rfl
  · exact False.elim hs
  · exact False.elim hs

theorem usefulTwoOfEq_active
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 3) (D : LabeledBlocks K A B a b)
    (u : K) {s : LabelledResidue m} (hs : ActiveTwo s) : usefulTwoOfEq ha D u s = D.C u := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim hs
  · rfl
  · exact False.elim hs

theorem usefulOneOfEq_inactive_eq
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 2) (D : LabeledBlocks K A B a b)
    (u v : K) {s : LabelledResidue m} (hs : ¬ ActiveOne s) :
    usefulOneOfEq ha D u s = usefulOneOfEq ha D v s := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim (hs trivial)
  · rfl
  · rfl

theorem usefulTwoOfEq_inactive_eq
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 3) (D : LabeledBlocks K A B a b)
    (u v : K) {s : LabelledResidue m} (hs : ¬ ActiveTwo s) :
    usefulTwoOfEq ha D u s = usefulTwoOfEq ha D v s := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · rfl
  · exact False.elim (hs trivial)
  · rfl

theorem usefulOneOfEq_activity_iff (ha : a = 2) (D : LabeledBlocks K A B a b)
    (rel : K → K → Prop) (hC : ∃ u v, rel u v ∧ D.C u ≠ D.C v)
    (s : LabelledResidue m) :
    (∃ u v, rel u v ∧ usefulOneOfEq ha D u s ≠ usefulOneOfEq ha D v s) ↔ ActiveOne s := by
  classical
  constructor
  · rintro ⟨u, v, _, hne⟩
    by_contra hs
    exact hne (usefulOneOfEq_inactive_eq ha D u v hs)
  · intro hs
    obtain ⟨u, v, huv, hne⟩ := hC
    refine ⟨u, v, huv, ?_⟩
    simpa only [usefulOneOfEq_active ha D u hs, usefulOneOfEq_active ha D v hs] using hne

theorem usefulTwoOfEq_activity_iff (ha : a = 3) (D : LabeledBlocks K A B a b)
    (rel : K → K → Prop) (hC : ∃ u v, rel u v ∧ D.C u ≠ D.C v)
    (s : LabelledResidue m) :
    (∃ u v, rel u v ∧ usefulTwoOfEq ha D u s ≠ usefulTwoOfEq ha D v s) ↔ ActiveTwo s := by
  classical
  constructor
  · rintro ⟨u, v, _, hne⟩
    by_contra hs
    exact hne (usefulTwoOfEq_inactive_eq ha D u v hs)
  · intro hs
    obtain ⟨u, v, huv, hne⟩ := hC
    refine ⟨u, v, huv, ?_⟩
    simpa only [usefulTwoOfEq_active ha D u hs, usefulTwoOfEq_active ha D v hs] using hne

end PeriodicTilingThree.SharedSeed

end

end OAI
