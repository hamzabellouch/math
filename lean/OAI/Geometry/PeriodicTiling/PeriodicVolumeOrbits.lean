import OAI.Geometry.PeriodicTiling.EuclideanBasic
import Mathlib.Algebra.Module.ZLattice.Basic

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

def representatives (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d)) : Set (Space d) :=
  C ∩ ZSpan.fundamentalDomain b

theorem representatives_finite (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hfin : ∀ K : Set (Space d), Bornology.IsBounded K → (C ∩ K).Finite) :
    (representatives b C).Finite :=
  hfin _ (ZSpan.fundamentalDomain_isBounded b)

def orbitMap (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (p : representatives b C × latticeOfBasis b) : C :=
  ⟨(p.1 : Space d) + (p.2 : Space d),
    (hp p.2 p.2.property p.1).2 p.1.property.1⟩

theorem orbitMap_injective (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v) :
    Function.Injective (orbitMap b C hp) := by
  rintro ⟨r, g⟩ ⟨s, h⟩ he
  have he' : (r : Space d) + (g : Space d) = s + (h : Space d) :=
    congrArg Subtype.val he
  have hr : ZSpan.fract b (r : Space d) = r :=
    ZSpan.fract_eq_self.mpr r.property.2
  have hs : ZSpan.fract b (s : Space d) = s :=
    ZSpan.fract_eq_self.mpr s.property.2
  have hfract := congrArg (ZSpan.fract b) he'
  rw [ZSpan.fract_add_ZSpan b _ g.property,
    ZSpan.fract_add_ZSpan b _ h.property, hr, hs] at hfract
  have hrs : r = s := Subtype.ext hfract
  subst s
  have hgh : g = h := Subtype.ext (add_left_cancel he')
  subst h
  rfl

theorem orbitMap_surjective (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v) :
    Function.Surjective (orbitMap b C hp) := by
  intro c
  let g : latticeOfBasis b := ZSpan.floor b (c : Space d)
  have hneg : -(g : Space d) ∈ latticeOfBasis b :=
    (latticeOfBasis b).neg_mem g.property
  have hc : ZSpan.fract b (c : Space d) ∈ C := by
    rw [ZSpan.fract_apply, sub_eq_add_neg]
    exact (hp _ hneg c).2 c.property
  let r : representatives b C :=
    ⟨ZSpan.fract b c, hc, ZSpan.fract_mem_fundamentalDomain b c⟩
  refine ⟨(r, g), Subtype.ext ?_⟩
  change ZSpan.fract b (c : Space d) + (ZSpan.floor b (c : Space d) : Space d) = c
  rw [ZSpan.fract_apply, sub_add_cancel]

def orbitEquiv (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v) :
    representatives b C × latticeOfBasis b ≃ C :=
  Equiv.ofBijective (orbitMap b C hp)
    ⟨orbitMap_injective b C hp, orbitMap_surjective b C hp⟩

@[simp] theorem orbitEquiv_apply_coe (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (r : representatives b C) (g : latticeOfBasis b) :
    ((orbitEquiv b C hp (r, g) : C) : Space d) = (r : Space d) + (g : Space d) :=
  rfl

theorem type_constant_on_orbit (b : Module.Basis (Fin d) ℝ (Space d))
    (C C1 : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (r : representatives b C) (g : latticeOfBasis b) :
    ((orbitEquiv b C hp (r, g) : C) : Space d) ∈ C1 ↔ (r : Space d) ∈ C1 :=
  ht g g.property r

end PeriodicTilingThree.PeriodicVolume

end

end OAI
