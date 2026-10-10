import Mathlib

namespace OAI


namespace Problem355.AuxiliaryCap

variable {F : Type*} [Field F]

def quad (η x y : F) : F := x ^ 2 - η * y ^ 2

theorem quad_eq_zero_iff {η : F} (hη : ¬ IsSquare η) (x y : F) :
    quad η x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hy : y = 0 := by
      by_contra hy
      apply hη
      refine ⟨x / y, ?_⟩
      have hxy : x ^ 2 = η * y ^ 2 := sub_eq_zero.mp h
      have heq : η = (x / y) ^ 2 := by
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hy)]
        exact hxy.symm
      simpa [pow_two] using heq
    refine ⟨?_, hy⟩
    simpa [quad, hy] using h
  · rintro ⟨rfl, rfl⟩
    simp [quad]

def graph (η : F) : Set (Fin 3 → F) :=
  {p | p 2 = quad η (p 0) (p 1)}

def linePoint (p q : Fin 3 → F) (t : F) : Fin 3 → F :=
  fun i => p i + t * (q i - p i)

theorem linePoint_mem_graph_iff {η : F} (hη : ¬ IsSquare η)
    {p q : Fin 3 → F} (hp : p ∈ graph η) (hq : q ∈ graph η)
    (hpq : p ≠ q) (t : F) :
    linePoint p q t ∈ graph η ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro ht
    have hqdiff : quad η (q 0 - p 0) (q 1 - p 1) ≠ 0 := by
      intro hzero
      obtain ⟨hx, hy⟩ := (quad_eq_zero_iff hη _ _).mp hzero
      have hx' : p 0 = q 0 := (sub_eq_zero.mp hx).symm
      have hy' : p 1 = q 1 := (sub_eq_zero.mp hy).symm
      apply hpq
      funext i
      fin_cases i
      · exact hx'
      · exact hy'
      · exact hp.trans ((congrArg₂ (quad η) hx' hy').trans hq.symm)
    have hprod : t * (t - 1) * quad η (q 0 - p 0) (q 1 - p 1) = 0 := by
      calc
        t * (t - 1) * quad η (q 0 - p 0) (q 1 - p 1) =
            quad η (linePoint p q t 0) (linePoint p q t 1) -
              linePoint p q t 2 := by
                change p 2 = quad η (p 0) (p 1) at hp
                change q 2 = quad η (q 0) (q 1) at hq
                dsimp [linePoint]
                rw [hp, hq]
                dsimp [quad]
                ring
        _ = 0 := sub_eq_zero.mpr ht.symm
    rcases (mul_eq_zero.mp hprod).resolve_right hqdiff with h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl)
    · simpa [graph, linePoint] using hp
    · simpa [graph, linePoint] using hq

theorem linePoint_eq_lineMap (p q : Fin 3 → F) (t : F) :
    linePoint p q t = AffineMap.lineMap p q t := by
  ext i
  simp [linePoint, AffineMap.lineMap_apply, add_comm]

theorem not_collinear_graph {η : F} (hη : ¬ IsSquare η)
    {p q r : Fin 3 → F} (hp : p ∈ graph η) (hq : q ∈ graph η)
    (hr : r ∈ graph η) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ Collinear F ({p, q, r} : Set (Fin 3 → F)) := by
  intro hcol
  have hrline := hcol.mem_affineSpan_of_mem_of_ne
    (by simp : p ∈ ({p, q, r} : Set (Fin 3 → F)))
    (by simp : q ∈ ({p, q, r} : Set (Fin 3 → F)))
    (by simp : r ∈ ({p, q, r} : Set (Fin 3 → F))) hpq
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hrline
  have htgraph : linePoint p q t ∈ graph η := by
    rw [linePoint_eq_lineMap, ht]
    exact hr
  rcases (linePoint_mem_graph_iff hη hp hq hpq t).mp htgraph with ht0 | ht1
  · subst t
    exact hpr (by simpa using ht)
  · subst t
    exact hqr (by simpa using ht)

def graphEquiv (η : F) : (F × F) ≃ graph η where
  toFun xy := ⟨![xy.1, xy.2, quad η xy.1 xy.2], by simp [graph]⟩
  invFun p := (p.val 0, p.val 1)
  left_inv xy := by simp
  right_inv p := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact p.property.symm

theorem card_graph [Fintype F] (η : F) :
    Nat.card (graph η) = Fintype.card F ^ 2 := by
  rw [Nat.card_congr (graphEquiv η).symm, Nat.card_prod,
    Nat.card_eq_fintype_card, pow_two]

def IsCap (S : Set (Fin 3 → F)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
    ¬ Collinear F ({p, q, r} : Set (Fin 3 → F))

theorem IsCap.mono {S T : Set (Fin 3 → F)} (hS : IsCap S) (hTS : T ⊆ S) :
    IsCap T := by
  intro p hp q hq r hr hpq hpr hqr
  exact hS p (hTS hp) q (hTS hq) r (hTS hr) hpq hpr hqr

theorem IsCap.image {S : Set (Fin 3 → F)} (hS : IsCap S)
    (f : (Fin 3 → F) →ᵃ[F] (Fin 3 → F)) (hf : Function.Injective f) :
    IsCap (f '' S) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩ hpq hpr hqr
  have hcol := hS p hp q hq r hr
    (fun h => hpq (congrArg f h)) (fun h => hpr (congrArg f h))
    (fun h => hqr (congrArg f h))
  have hai := (affineIndependent_iff_not_collinear_set).mpr hcol
  have himage := hai.map' f hf
  apply (affineIndependent_iff_not_collinear_set).mp
  convert himage using 1
  funext i
  fin_cases i <;> rfl

theorem IsCap.translate {S : Set (Fin 3 → F)} (hS : IsCap S) (a : Fin 3 → F) :
    IsCap ((fun p => a + p) '' S) := by
  exact hS.image (AffineEquiv.constVAdd F (Fin 3 → F) a).toAffineMap
    (AffineEquiv.constVAdd F (Fin 3 → F) a).injective

theorem isCap_graph {η : F} (hη : ¬ IsSquare η) : IsCap (graph η) := by
  intro p hp q hq r hr hpq hpr hqr
  exact not_collinear_graph hη hp hq hr hpq hpr hqr

noncomputable def graphFinset [Fintype F] (η : F) : Finset (Fin 3 → F) :=
  (Set.toFinite (graph η)).toFinset

@[simp] theorem mem_graphFinset [Fintype F] (η : F) (p : Fin 3 → F) :
    p ∈ graphFinset η ↔ p ∈ graph η := by
  simp [graphFinset]

@[simp] theorem card_graphFinset [Fintype F] (η : F) :
    (graphFinset η).card = Fintype.card F ^ 2 := by
  rw [graphFinset, ← Set.ncard_eq_toFinset_card]
  exact card_graph η

theorem exists_finset_cap [Fintype F] (hF : ringChar F ≠ 2) :
    ∃ S : Finset (Fin 3 → F), S.card = Fintype.card F ^ 2 ∧ IsCap (S : Set (Fin 3 → F)) := by
  obtain ⟨η, hη⟩ := FiniteField.exists_nonsquare hF
  refine ⟨graphFinset η, card_graphFinset η, ?_⟩
  simpa [graphFinset] using isCap_graph hη

theorem exists_graph_cap [Finite F] (hF : ringChar F ≠ 2) :
    ∃ η : F, ∀ p ∈ graph η, ∀ q ∈ graph η, p ≠ q →
      ∀ t : F, linePoint p q t ∈ graph η ↔ t = 0 ∨ t = 1 := by
  obtain ⟨η, hη⟩ := FiniteField.exists_nonsquare hF
  exact ⟨η, fun _ hp _ hq hpq t => linePoint_mem_graph_iff hη hp hq hpq t⟩

end Problem355.AuxiliaryCap

end OAI
