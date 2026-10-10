import OAI.Algebra.Finitistic.Selection.GroupSelection
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Tactic.DeriveFintype

namespace OAI
open scoped commutatorElement
namespace LittleFinitistic.FinitePresentation

/-! Target: Group.IsFinitelyPresented Presentation.AuxiliaryGroup.
Section 2, Lemma group-finite-presentation. No finite-presentation hypothesis
is permitted on the target group. Diagonal W generators are redundant.
-/

section Orbit
variable {G : Type*} [Group G]

def orbit (t x : G) (r : ℤ) : G := t ^ r * x * (t ^ r)⁻¹

@[simp] theorem orbit_zero (t x : G) : orbit t x 0 = x := by simp [orbit]

theorem orbit_add (t x : G) (a b : ℤ) :
    orbit t (orbit t x b) a = orbit t x (a+b) := by
  simp only [orbit, zpow_add, mul_inv_rev]
  group

theorem orbit_commute (t q x : G) (h : Commute t q) (a : ℤ) :
    t * orbit q x a * t⁻¹ = orbit q (t*x*t⁻¹) a := by
  have hc := h.zpow_right a
  simp only [orbit]
  calc
    t * (q^a*x*(q^a)⁻¹) * t⁻¹ = (t*q^a)*x*(q^a)⁻¹*t⁻¹ := by group
    _ = (q^a*t)*x*(q^a)⁻¹*t⁻¹ := by rw [hc.eq]
    _ = q^a*(t*x)*((q^a)⁻¹*t⁻¹) := by group
    _ = q^a*(t*x)*(t⁻¹*(q^a)⁻¹) := by rw [hc.inv_inv.eq]
    _ = q^a*(t*x*t⁻¹)*(q^a)⁻¹ := by group

theorem orbit_covariance (t q x : G) (h : Commute t q) (d : ℤ)
    (hx : t*x*t⁻¹ = orbit q x d) (a : ℤ) :
    t * orbit q x a * t⁻¹ = orbit q x (a+d) := by
  rw [orbit_commute t q x h a, hx, orbit_add]

theorem family_zpow (t : G) (f : ℤ → G) (d : ℤ)
    (h : ∀ r, t*f r*t⁻¹ = f (r+d)) (n r : ℤ) :
    orbit t (f r) n = f (r+n*d) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have he : (↑n + 1 : ℤ) = 1 + ↑n := by omega
      rw [he, ← orbit_add, ih]
      change t^ (1:ℤ) * _ * (t^(1:ℤ))⁻¹ = _
      simp only [zpow_one, h]
      congr 1
      ring
  | pred n ih =>
      have hi := h (r + (-↑n - 1)*d)
      have he : r + (-↑n - 1)*d+d = r+(-↑n)*d := by ring
      rw [he] at hi
      have he' : (-↑n - 1 : ℤ) = -1 + -↑n := by omega
      rw [he', ← orbit_add, ih, ← hi]
      simp only [orbit, zpow_neg_one, inv_inv]
      group

end Orbit

abbrev Lattice := Fin 3 → ℤ

def coord (i : Fin 3) (r : ℤ) : Lattice := fun h => if h=i then r else 0

def wtU (i : Fin 3) (n : Lattice) := -n i

def wtV (i : Fin 3) (n : Lattice) := n i

def wtW (i j : Fin 3) (n : Lattice) := n i-n j

/- Each theorem supplies the integral preimage in the corresponding table row. -/
theorem table_UU (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtU i n = r ∧ wtU j n = s := by
  refine ⟨coord i (-r) + coord j (-s), ?_⟩
  simp [wtU, coord, hij, hij.symm]

theorem table_VV (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtV i n = r ∧ wtV j n = s := by
  refine ⟨coord i r + coord j s, ?_⟩
  simp [wtV, coord, hij, hij.symm]

theorem table_UV (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtU i n = r ∧ wtV j n = s := by
  refine ⟨coord i (-r) + coord j s, ?_⟩
  simp [wtU, wtV, coord, hij, hij.symm]

theorem table_WU (i j h : Fin 3) (hij : i ≠ j) (hhi : h ≠ i) (r s : ℤ) :
    ∃ n : Lattice, wtW i j n = r ∧ wtU h n = s := by
  by_cases hhj : h=j
  · subst h
    refine ⟨coord i (r-s) + coord j (-s), ?_⟩
    simp [wtW, wtU, coord, hij, hij.symm]
  · refine ⟨coord i r + coord h (-s), ?_⟩
    simp [wtW, wtU, coord, hij.symm, hhi, (Ne.symm hhi), (Ne.symm hhj)]

theorem table_WV (i j h : Fin 3) (hij : i ≠ j) (hhj : h ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtW i j n = r ∧ wtV h n = s := by
  by_cases hhi : h=i
  · subst h
    refine ⟨coord i s + coord j (s-r), ?_⟩
    simp [wtW, wtV, coord, hij, hij.symm]
  · refine ⟨coord i r + coord h s, ?_⟩
    simp [wtW, wtV, coord, hij.symm, hhi, (Ne.symm hhi), (Ne.symm hhj)]

theorem table_UW (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtU i n = r ∧ wtW i j n = s := by
  refine ⟨coord i (-r) + coord j (-r-s), ?_⟩
  simp [wtU, wtW, coord, hij, hij.symm]

theorem table_WV_output (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtW i j n = r ∧ wtV j n = s := by
  refine ⟨coord i (r+s) + coord j s, ?_⟩
  simp [wtW, wtV, coord, hij, hij.symm]


section Torus
variable {G : Type*} [Group G]

def torus (T : Fin 3 → G) (n : Lattice) : G := T 0 ^ n 0 * T 1 ^ n 1 * T 2 ^ n 2

theorem family_torus (T : Fin 3 → G) (f : ℤ → G) (d : Fin 3 → ℤ)
    (hf : ∀ l r, T l * f r * (T l)⁻¹ = f (r+d l)) (n : Lattice) (r : ℤ) :
    torus T n * f r * (torus T n)⁻¹ =
      f (r + n 0*d 0 + n 1*d 1 + n 2*d 2) := by
  have he : torus T n * f r * (torus T n)⁻¹ =
      orbit (T 0) (orbit (T 1) (orbit (T 2) (f r) (n 2)) (n 1)) (n 0) := by
    simp only [torus, orbit]
    group
  rw [he, family_zpow _ _ _ (hf 2), family_zpow _ _ _ (hf 1),
    family_zpow _ _ _ (hf 0)]
  congr 1
  ring

theorem torus_U (T : Fin 3 → G) (U : Fin 3 → ℤ → G)
    (hf : ∀ l i r, T l * U i r * (T l)⁻¹ = U i (r-if l=i then 1 else 0))
    (n : Lattice) (i : Fin 3) (r : ℤ) :
    torus T n * U i r * (torus T n)⁻¹ = U i (r+wtU i n) := by
  have h := family_torus T (U i) (fun l => -(if l=i then 1 else 0))
    (fun l r => by simpa only [sub_eq_add_neg] using hf l i r) n r
  convert h using 2; fin_cases i <;> simp [wtU]

theorem torus_V (T : Fin 3 → G) (V : Fin 3 → ℤ → G)
    (hf : ∀ l i r, T l * V i r * (T l)⁻¹ = V i (r+if l=i then 1 else 0))
    (n : Lattice) (i : Fin 3) (r : ℤ) :
    torus T n * V i r * (torus T n)⁻¹ = V i (r+wtV i n) := by
  have h := family_torus T (V i) (fun l => if l=i then 1 else 0)
    (fun l r => hf l i r) n r
  convert h using 2; fin_cases i <;> simp [wtV]

theorem torus_W (T : Fin 3 → G) (W : Fin 3 → Fin 3 → ℤ → G)
    (hf : ∀ l i j r, T l * W i j r * (T l)⁻¹ =
      W i j (r+(if l=i then 1 else 0)-if l=j then 1 else 0))
    (n : Lattice) (i j : Fin 3) (r : ℤ) :
    torus T n * W i j r * (torus T n)⁻¹ = W i j (r+wtW i j n) := by
  have h := family_torus T (W i j) (fun l => (if l=i then 1 else 0)-(if l=j then 1 else 0))
    (fun l r => by simpa only [add_sub_assoc] using hf l i j r) n r
  convert h using 2; fin_cases i <;> fin_cases j <;> simp [wtW] <;> ring
end Torus


/-- Intermediate data: covariance plus only zero-argument algebraic relations.
This is constructed below from a finite presented group, not postulated for it. -/
structure CovariantData (G : Type*) [Group G] where
  T : Fin 3 → G
  U : Fin 3 → ℤ → G
  V : Fin 3 → ℤ → G
  W : Fin 3 → Fin 3 → ℤ → G
  TT : ∀ i j, Commute (T i) (T j)
  TU : ∀ l i a, T l * U i a * (T l)⁻¹ = U i (a-if l=i then 1 else 0)
  TV : ∀ l i a, T l * V i a * (T l)⁻¹ = V i (a+if l=i then 1 else 0)
  TW : ∀ l i j a, T l * W i j a * (T l)⁻¹ =
    W i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0)
  diagonal : ∀ i a, W i i a = 1
  square : ∀ i, U i 0 * U i 0 = 1
  UU : ∀ i j, i ≠ j → Commute (U i 0) (U j 0)
  VV : ∀ i j, i ≠ j → Commute (V i 0) (V j 0)
  UV : ∀ i j, i ≠ j → Commute (U i 0) (V j 0)
  WU : ∀ i j h, h ≠ i → Commute (W i j 0) (U h 0)
  WV : ∀ i j h, h ≠ j → Commute (W i j 0) (V h 0)
  UWout : ∀ i j, i ≠ j → ⁅U i 0,W i j 0⁆ = U j 0
  WVout : ∀ i j, i ≠ j → ⁅W i j 0,V j 0⁆ = V i 0

namespace CovariantData
variable {G : Type*} [Group G] (D : CovariantData G)

def act (n : Lattice) : G ≃* G := MulAut.conj (torus D.T n)

@[simp] theorem act_U (n : Lattice) (i : Fin 3) (a : ℤ) :
    D.act n (D.U i a) = D.U i (a+wtU i n) := torus_U D.T D.U D.TU n i a
@[simp] theorem act_V (n : Lattice) (i : Fin 3) (a : ℤ) :
    D.act n (D.V i a) = D.V i (a+wtV i n) := torus_V D.T D.V D.TV n i a
@[simp] theorem act_W (n : Lattice) (i j : Fin 3) (a : ℤ) :
    D.act n (D.W i j a) = D.W i j (a+wtW i j n) := torus_W D.T D.W D.TW n i j a

/-- All infinite relators follow from the finite zero-argument patterns. -/
def toSelection : SelectionGroupData G where
  T := D.T
  U := D.U
  V := D.V
  W := D.W
  commute_TT := D.TT
  conj_TU := D.TU
  conj_TV := D.TV
  conj_TW := D.TW
  diagonal_W := D.diagonal
  square_U i a := by
    have ha : wtU i (coord i (-a)) = a := by simp [wtU, coord]
    have h := congrArg (D.act (coord i (-a))) (D.square i)
    simpa only [map_mul, map_one, act_U, zero_add, ha] using h
  commute_UU i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_UU i j hij a b
    have h := (D.UU i j hij).map (D.act n)
    simpa only [act_U, zero_add, ha, hb] using h
  commute_VV i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_VV i j hij a b
    have h := (D.VV i j hij).map (D.act n)
    simpa only [act_V, zero_add, ha, hb] using h
  commute_UV i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_UV i j hij a b
    have h := (D.UV i j hij).map (D.act n)
    simpa only [act_U, act_V, zero_add, ha, hb] using h
  commute_WU i j h a b hhi := by
    by_cases hij : i=j
    · subst j
      rw [D.diagonal]
      exact Commute.one_left _
    · obtain ⟨n, ha, hb⟩ := table_WU i j h hij hhi a b
      have hh := (D.WU i j h hhi).map (D.act n)
      simpa only [act_U, act_W, zero_add, ha, hb] using hh
  commute_WV i j h a b hhj := by
    by_cases hij : i=j
    · subst j
      rw [D.diagonal]
      exact Commute.one_left _
    · obtain ⟨n, ha, hb⟩ := table_WV i j h hij hhj a b
      have hh := (D.WV i j h hhj).map (D.act n)
      simpa only [act_V, act_W, zero_add, ha, hb] using hh
  commutator_UW i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_UW i j hij a b
    have hout : wtU j n = a+b := by dsimp [wtU, wtW] at *; omega
    have h := congrArg (D.act n) (D.UWout i j hij)
    simpa only [map_commutatorElement, act_U, act_W, zero_add, ha, hb, hout] using h
  commutator_WV i j a b hij := by
    obtain ⟨n, ha, hb⟩ := table_WV_output i j hij a b
    have hout : wtV i n = a+b := by dsimp [wtV, wtW] at *; omega
    have h := congrArg (D.act n) (D.WVout i j hij)
    simpa only [map_commutatorElement, act_V, act_W, zero_add, ha, hb, hout] using h
end CovariantData

/-- Finitely many seed values. Diagonal W seeds will be killed. -/
structure SeedValues (G : Type*) where
  T : Fin 3 → G
  u : Fin 3 → G
  v : Fin 3 → G
  w : Fin 3 → Fin 3 → G

structure SeedData (G : Type*) [Group G] extends SeedValues G where
  TT : ∀ i j, Commute (T i) (T j)
  Tu : ∀ l i, T l*u i*(T l)⁻¹ = orbit (T i) (u i) (if l=i then 1 else 0)
  Tv : ∀ l i, T l*v i*(T l)⁻¹ = orbit (T i) (v i) (if l=i then 1 else 0)
  Tw : ∀ l i j, T l*w i j*(T l)⁻¹ =
    orbit (T i) (w i j) ((if l=i then 1 else 0)-(if l=j then 1 else 0))
  diagonal : ∀ i, w i i = 1
  square : ∀ i, u i*u i = 1
  UU : ∀ i j, i ≠ j → Commute (u i) (u j)
  VV : ∀ i j, i ≠ j → Commute (v i) (v j)
  UV : ∀ i j, i ≠ j → Commute (u i) (v j)
  WU : ∀ i j h, h ≠ i → Commute (w i j) (u h)
  WV : ∀ i j h, h ≠ j → Commute (w i j) (v h)
  UWout : ∀ i j, i ≠ j → ⁅u i,w i j⁆ = u j
  WVout : ∀ i j, i ≠ j → ⁅w i j,v j⁆ = v i

namespace SeedData
variable {G : Type*} [Group G] (D : SeedData G)

def toCovariant : CovariantData G where
  T := D.T
  U i r := orbit (D.T i) (D.u i) (-r)
  V i r := orbit (D.T i) (D.v i) r
  W i j r := orbit (D.T i) (D.w i j) r
  TT := D.TT
  TU l i a := by
    rw [orbit_covariance _ _ _ (D.TT l i) _ (D.Tu l i)]
    congr 1
    omega
  TV l i a := orbit_covariance _ _ _ (D.TT l i) _ (D.Tv l i) a
  TW l i j a := by
    rw [orbit_covariance _ _ _ (D.TT l i) _ (D.Tw l i j)]
    congr 1
    omega
  diagonal i a := by simp [orbit, D.diagonal]
  square i := by simpa using D.square i
  UU i j h := by simpa using D.UU i j h
  VV i j h := by simpa using D.VV i j h
  UV i j h := by simpa using D.UV i j h
  WU i j h hh := by simpa using D.WU i j h hh
  WV i j h hh := by simpa using D.WV i j h hh
  UWout i j h := by simpa using D.UWout i j h
  WVout i j h := by simpa using D.WVout i j h

def toSelection : SelectionGroupData G := D.toCovariant.toSelection
end SeedData


inductive SeedGenerator where
  | T : Fin 3 → SeedGenerator
  | U : Fin 3 → SeedGenerator
  | V : Fin 3 → SeedGenerator
  | W : Fin 3 → Fin 3 → SeedGenerator
  deriving DecidableEq, Fintype

inductive Rule where
  | TT : Fin 3 → Fin 3 → Rule
  | Tu : Fin 3 → Fin 3 → Rule
  | Tv : Fin 3 → Fin 3 → Rule
  | Tw : Fin 3 → Fin 3 → Fin 3 → Rule
  | diagonal : Fin 3 → Rule
  | square : Fin 3 → Rule
  | UU : Fin 3 → Fin 3 → Rule
  | VV : Fin 3 → Fin 3 → Rule
  | UV : Fin 3 → Fin 3 → Rule
  | WU : Fin 3 → Fin 3 → Fin 3 → Rule
  | WV : Fin 3 → Fin 3 → Fin 3 → Rule
  | UWout : Fin 3 → Fin 3 → Rule
  | WVout : Fin 3 → Fin 3 → Rule
  deriving DecidableEq, Fintype

/-- Finite seed equation patterns. Vacuous index combinations give 1=1. -/
def equation {G : Type*} [Group G] (D : SeedValues G) : Rule → G × G
  | .TT i j => (D.T i*D.T j, D.T j*D.T i)
  | .Tu l i => (D.T l*D.u i*(D.T l)⁻¹, orbit (D.T i) (D.u i) (if l=i then 1 else 0))
  | .Tv l i => (D.T l*D.v i*(D.T l)⁻¹, orbit (D.T i) (D.v i) (if l=i then 1 else 0))
  | .Tw l i j => (D.T l*D.w i j*(D.T l)⁻¹,
      orbit (D.T i) (D.w i j) ((if l=i then 1 else 0)-(if l=j then 1 else 0)))
  | .diagonal i => (D.w i i, 1)
  | .square i => (D.u i*D.u i, 1)
  | .UU i j => if i≠j then (D.u i*D.u j, D.u j*D.u i) else (1,1)
  | .VV i j => if i≠j then (D.v i*D.v j, D.v j*D.v i) else (1,1)
  | .UV i j => if i≠j then (D.u i*D.v j, D.v j*D.u i) else (1,1)
  | .WU i j h => if h≠i then (D.w i j*D.u h, D.u h*D.w i j) else (1,1)
  | .WV i j h => if h≠j then (D.w i j*D.v h, D.v h*D.w i j) else (1,1)
  | .UWout i j => if i≠j then (⁅D.u i,D.w i j⁆, D.u j) else (1,1)
  | .WVout i j => if i≠j then (⁅D.w i j,D.v j⁆, D.v i) else (1,1)

def freeSeeds : SeedValues (FreeGroup SeedGenerator) where
  T i := FreeGroup.of (.T i)
  u i := FreeGroup.of (.U i)
  v i := FreeGroup.of (.V i)
  w i j := FreeGroup.of (.W i j)

def evalSeeds {G : Type*} (D : SeedValues G) : SeedGenerator → G
  | .T i => D.T i
  | .U i => D.u i
  | .V i => D.v i
  | .W i j => D.w i j

theorem equation_evaluate {G : Type*} [Group G] (D : SeedValues G) (r : Rule) :
    FreeGroup.lift (evalSeeds D) (equation freeSeeds r).1 = (equation D r).1 ∧
    FreeGroup.lift (evalSeeds D) (equation freeSeeds r).2 = (equation D r).2 := by
  cases r <;> dsimp only [equation] <;> (try split_ifs) <;> simp [orbit, freeSeeds, evalSeeds]

def relator (r : Rule) : FreeGroup SeedGenerator :=
  (equation freeSeeds r).1 * (equation freeSeeds r).2⁻¹

def finiteRelators : Set (FreeGroup SeedGenerator) := Set.range relator
abbrev Model := PresentedGroup finiteRelators

instance : Finite finiteRelators := Set.finite_range relator
instance : Group.IsFinitelyPresented Model := inferInstance

def modelValues : SeedValues Model where
  T i := PresentedGroup.of (.T i)
  u i := PresentedGroup.of (.U i)
  v i := PresentedGroup.of (.V i)
  w i j := PresentedGroup.of (.W i j)

theorem model_equation (r : Rule) :
    (equation modelValues r).1 = (equation modelValues r).2 := by
  have hm : FreeGroup.lift (evalSeeds modelValues) = PresentedGroup.mk finiteRelators := by
    apply FreeGroup.ext_hom
    intro s
    cases s <;> rfl
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := finiteRelators)
    (x := (equation freeSeeds r).1) (y := (equation freeSeeds r).2) ⟨r,rfl⟩
  obtain ⟨h₁,h₂⟩ := equation_evaluate modelValues r
  rw [hm] at h₁ h₂
  exact h₁.symm.trans (h.trans h₂)

def modelSeedData : SeedData Model where
  toSeedValues := modelValues
  TT i j := by simpa [equation, Commute, SemiconjBy] using model_equation (.TT i j)
  Tu l i := model_equation (.Tu l i)
  Tv l i := model_equation (.Tv l i)
  Tw l i j := model_equation (.Tw l i j)
  diagonal i := model_equation (.diagonal i)
  square i := model_equation (.square i)
  UU i j h := by simpa [equation, h, Commute, SemiconjBy] using model_equation (.UU i j)
  VV i j h := by simpa [equation, h, Commute, SemiconjBy] using model_equation (.VV i j)
  UV i j h := by simpa [equation, h, Commute, SemiconjBy] using model_equation (.UV i j)
  WU i j h hh := by simpa [equation, hh, Commute, SemiconjBy] using model_equation (.WU i j h)
  WV i j h hh := by simpa [equation, hh, Commute, SemiconjBy] using model_equation (.WV i j h)
  UWout i j h := by simpa [equation, h] using model_equation (.UWout i j)
  WVout i j h := by simpa [equation, h] using model_equation (.WVout i j)

/-- The homomorphism from the supplied infinite presentation to the finite model. -/
def toModel : Presentation.AuxiliaryGroup →* Model :=
  Presentation.ofData modelSeedData.toSelection


section OriginalSeeds
variable {G : Type*} [Group G] (D : SelectionGroupData G)

@[simp] theorem selection_U_orbit (i : Fin 3) (a : ℤ) :
    orbit (D.T i) (D.U i 0) (-a) = D.U i a := by
  have h := family_zpow (D.T i) (D.U i) (-1)
    (fun r => by simpa only [ite_true, sub_eq_add_neg] using D.conj_TU i i r) (-a) 0
  simpa using h

@[simp] theorem selection_V_orbit (i : Fin 3) (a : ℤ) :
    orbit (D.T i) (D.V i 0) a = D.V i a := by
  have h := family_zpow (D.T i) (D.V i) 1
    (fun r => by simpa only [ite_true] using D.conj_TV i i r) a 0
  simpa using h

@[simp] theorem selection_W_orbit (i j : Fin 3) (a : ℤ) :
    orbit (D.T i) (D.W i j 0) a = D.W i j a := by
  by_cases hij : i=j
  · subst j
    simp [orbit, D.diagonal_W]
  · have h := family_zpow (D.T i) (D.W i j) 1
      (fun r => by simpa [hij] using D.conj_TW i i j r) a 0
    simpa using h

/-- The original presentation satisfies each of the finite seed equations. -/
def originalSeeds : SeedData G where
  T := D.T
  u i := D.U i 0
  v i := D.V i 0
  w i j := D.W i j 0
  TT := D.commute_TT
  Tu l i := by
    have h := D.conj_TU l i 0
    have hh := selection_U_orbit D i (-(if l=i then 1 else 0))
    simp only [neg_neg] at hh
    rw [hh]
    simpa using h
  Tv l i := by
    rw [selection_V_orbit]
    simpa using D.conj_TV l i 0
  Tw l i j := by
    rw [selection_W_orbit]
    simpa using D.conj_TW l i j 0
  diagonal i := D.diagonal_W i 0
  square i := D.square_U i 0
  UU i j h := D.commute_UU i j 0 0 h
  VV i j h := D.commute_VV i j 0 0 h
  UV i j h := D.commute_UV i j 0 0 h
  WU i j h hh := D.commute_WU i j h 0 0 hh
  WV i j h hh := D.commute_WV i j h 0 0 hh
  UWout i j h := by simpa using D.commutator_UW i j 0 0 h
  WVout i j h := by simpa using D.commutator_WV i j 0 0 h
end OriginalSeeds

theorem seed_equation {G : Type*} [Group G] (D : SeedData G) (r : Rule) :
    (equation D.toSeedValues r).1 = (equation D.toSeedValues r).2 := by
  cases r with
  | TT i j => exact (D.TT i j).eq
  | Tu l i => exact D.Tu l i
  | Tv l i => exact D.Tv l i
  | Tw l i j => exact D.Tw l i j
  | diagonal i => exact D.diagonal i
  | square i => exact D.square i
  | UU i j =>
      by_cases h : i≠j
      · simpa only [equation, ite_eq_left h] using (D.UU i j h).eq
      · simp [equation, h]
  | VV i j =>
      by_cases h : i≠j
      · simpa only [equation, ite_eq_left h] using (D.VV i j h).eq
      · simp [equation, h]
  | UV i j =>
      by_cases h : i≠j
      · simpa only [equation, ite_eq_left h] using (D.UV i j h).eq
      · simp [equation, h]
  | WU i j k =>
      by_cases h : k≠i
      · simpa only [equation, ite_eq_left h] using (D.WU i j k h).eq
      · simp [equation, h]
  | WV i j k =>
      by_cases h : k≠j
      · simpa only [equation, ite_eq_left h] using (D.WV i j k h).eq
      · simp [equation, h]
  | UWout i j => by_cases h : i≠j <;> simp [equation, h, (D.UWout i j)]
  | WVout i j => by_cases h : i≠j <;> simp [equation, h, (D.WVout i j)]

/-- Universal evaluation of the finite presentation in any proved seed data. -/
def modelLift {G : Type*} [Group G] (D : SeedData G) : Model →* G :=
  PresentedGroup.toGroup (f := evalSeeds D.toSeedValues) (by
    intro r hr
    obtain ⟨s,rfl⟩ := hr
    dsimp only [relator]
    rw [map_mul, map_inv, (equation_evaluate D.toSeedValues s).1,
      (equation_evaluate D.toSeedValues s).2, seed_equation D s, mul_inv_cancel])

@[simp] theorem modelLift_of {G : Type*} [Group G] (D : SeedData G) (s : SeedGenerator) :
    modelLift D (PresentedGroup.of s) = evalSeeds D.toSeedValues s := PresentedGroup.toGroup.of _

def fromModel : Model →* Presentation.AuxiliaryGroup :=
  modelLift (originalSeeds Presentation.data)


@[simp] theorem map_orbit {G H : Type*} [Group G] [Group H] (f : G →* H)
    (t x : G) (a : ℤ) : f (orbit t x a) = orbit (f t) (f x) a := by simp [orbit]

@[simp] theorem toModel_T (i : Fin 3) :
    toModel (Presentation.data.T i) = modelValues.T i :=
  Presentation.ofData_of modelSeedData.toSelection (.T i)
@[simp] theorem toModel_U (i : Fin 3) (a : ℤ) :
    toModel (Presentation.data.U i a) = orbit (modelValues.T i) (modelValues.u i) (-a) :=
  Presentation.ofData_of modelSeedData.toSelection (.U i a)
@[simp] theorem toModel_V (i : Fin 3) (a : ℤ) :
    toModel (Presentation.data.V i a) = orbit (modelValues.T i) (modelValues.v i) a :=
  Presentation.ofData_of modelSeedData.toSelection (.V i a)
@[simp] theorem toModel_W (i j : Fin 3) (a : ℤ) :
    toModel (Presentation.data.W i j a) = orbit (modelValues.T i) (modelValues.w i j) a :=
  Presentation.ofData_of modelSeedData.toSelection (.W i j a)

@[simp] theorem fromModel_T (i : Fin 3) :
    fromModel (modelValues.T i) = Presentation.data.T i :=
  modelLift_of (originalSeeds Presentation.data) (.T i)
@[simp] theorem fromModel_u (i : Fin 3) :
    fromModel (modelValues.u i) = Presentation.data.U i 0 :=
  modelLift_of (originalSeeds Presentation.data) (.U i)
@[simp] theorem fromModel_v (i : Fin 3) :
    fromModel (modelValues.v i) = Presentation.data.V i 0 :=
  modelLift_of (originalSeeds Presentation.data) (.V i)
@[simp] theorem fromModel_w (i j : Fin 3) :
    fromModel (modelValues.w i j) = Presentation.data.W i j 0 :=
  modelLift_of (originalSeeds Presentation.data) (.W i j)

theorem fromModel_toModel : fromModel.comp toModel = MonoidHom.id Presentation.AuxiliaryGroup := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      change fromModel (toModel (Presentation.data.T i)) = Presentation.data.T i
      simp
  | U i a =>
      change fromModel (toModel (Presentation.data.U i a)) = Presentation.data.U i a
      simp
  | V i a =>
      change fromModel (toModel (Presentation.data.V i a)) = Presentation.data.V i a
      simp
  | W i j a =>
      change fromModel (toModel (Presentation.data.W i j a)) = Presentation.data.W i j a
      simp

theorem toModel_fromModel : toModel.comp fromModel = MonoidHom.id Model := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      change toModel (fromModel (modelValues.T i)) = modelValues.T i
      simp
  | U i =>
      change toModel (fromModel (modelValues.u i)) = modelValues.u i
      simp
  | V i =>
      change toModel (fromModel (modelValues.v i)) = modelValues.v i
      simp
  | W i j =>
      change toModel (fromModel (modelValues.w i j)) = modelValues.w i j
      simp

/-- Equivalence of the explicit finite presentation and the supplied infinite presentation. -/
def presentationEquiv : Model ≃* Presentation.AuxiliaryGroup where
  toFun := fromModel
  invFun := toModel
  left_inv x := DFunLike.congr_fun toModel_fromModel x
  right_inv x := DFunLike.congr_fun fromModel_toModel x
  map_mul' := fromModel.map_mul

/-- Section 2, Lemma group-finite-presentation, for the exact supplied AuxiliaryGroup. -/
theorem auxiliaryGroup_isFinitelyPresented :
    Group.IsFinitelyPresented Presentation.AuxiliaryGroup :=
  Group.IsFinitelyPresented.equiv presentationEquiv

/-- The finite model retains the three redundant diagonal W generators. -/
theorem seedGenerator_card : Fintype.card SeedGenerator = 18 := by decide
/-- Number of indexed finite equation patterns, including tautological cases. -/
theorem rule_card : Fintype.card Rule = 159 := by decide +kernel

theorem model_isFinitelyPresented : Group.IsFinitelyPresented Model := inferInstance
end LittleFinitistic.FinitePresentation

end OAI
