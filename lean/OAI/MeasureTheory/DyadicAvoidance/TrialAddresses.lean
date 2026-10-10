import OAI.MeasureTheory.DyadicAvoidance.GridSeparation

namespace OAI

universe u_E u_I u_C u_L

noncomputable section

namespace Problem310.TrialAddresses

open GridSeparation

/-- Coordinates of a finite family of dyadic tables. Different table names
are different coordinates even when their numeric cell keys coincide. -/
abbrev GridAddress {E : Type u_E} (b : E → ℕ) := Σ e : E, Fin (2 ^ (b e + 2))

def centerAddress {E : Type u_E} (b : E → ℕ) (x : ℝ) (e : E) : GridAddress b :=
  ⟨e, dyadicKey (b e) x⟩

theorem centerAddress_injective {E : Type u_E} (b : E → ℕ) (x : ℝ) :
    Function.Injective (centerAddress b x) := by
  intro i j h
  exact congrArg Sigma.fst h

/-- Refinement preserves all equalities needed to recover a coarse key. -/
theorem dyadicKey_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (h : dyadicKey B x = dyadicKey B y) : dyadicKey b x = dyadicKey b y := by
  rw [dyadicKey_eq_iff]
  exact periodicKey_dyadic_eq_of_refine hb ((dyadicKey_eq_iff B x y).mp h)

def trialAddress {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (i : I) : GridAddress b :=
  ⟨edge i, dyadicKey (b (edge i)) (x + t * (2 : ℝ)⁻¹ ^ n i)⟩

/-- A tested coordinate is distinct from every center-exposed coordinate. -/
theorem trialAddress_ne_center {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i)) (i : I) (e : E) :
    trialAddress b edge n x t i ≠ centerAddress b x e := by
  intro h
  have he : edge i = e := congrArg Sigma.fst h
  subst e
  have hv := congrArg (fun z : GridAddress b => z.2.val) h
  have hk : dyadicKey (b (edge i)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (b (edge i)) x := Fin.ext hv
  exact (dyadicKey_ne_center (hnlo i) (hnhi i) htlo hthi) hk.symm

/-- The entire fresh trial-coordinate set is disjoint from the full center
exposure, including tables outside the center's actual route. -/
theorem trialAddress_disjoint_center {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i)) :
    Disjoint (Set.range (trialAddress b edge n x t))
      (Set.range (centerAddress b x)) := by
  rw [Set.disjoint_left]
  rintro z ⟨i, rfl⟩ ⟨e, he⟩
  exact trialAddress_ne_center b edge n x t htlo hthi hnlo hnhi i e he.symm

/-- Distinct table/index pairs give distinct fresh selector coordinates. -/
theorem trialAddress_injective {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (edge i))
    (hpair : Function.Injective (fun i => (edge i, n i))) :
    Function.Injective (trialAddress b edge n x t) := by
  intro i j h
  have he : edge i = edge j := congrArg Sigma.fst h
  have hv := congrArg (fun z : GridAddress b => z.2.val) h
  change (dyadicKey (b (edge i)) _).val = (dyadicKey (b (edge j)) _).val at hv
  rw [he] at hv
  have hk : dyadicKey (b (edge j)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (b (edge j)) (x + t * (2 : ℝ)⁻¹ ^ n j) := Fin.ext hv
  have hi : n i ≤ b (edge j) := he ▸ hnhi i
  have hn : n i = n j :=
    dyadicKey_injOn (a := 3) (by omega) htlo hthi
      ⟨hnlo i, hi⟩ ⟨hnlo j, hnhi j⟩ hk
  exact hpair (Prod.ext he hn)

/-- Adaptive terminal addresses are injective whenever equal leaves force
the same child subtree, and each terminal resolution refines that child's
incoming grid. The leaf selection may otherwise depend arbitrarily on all
selector tables. -/
theorem terminalAddress_injective {I : Type u_I} {C : Type u_C} {L : Type u_L}
    (child : I → C) (n : I → ℕ) (leaf : I → L)
    (b : C → ℕ) (B : L → ℕ) (x t : ℝ)
    (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (child i))
    (hrefine : ∀ i, b (child i) ≤ B (leaf i))
    (hbranch : ∀ i j, leaf i = leaf j → child i = child j)
    (hpair : Function.Injective (fun i => (child i, n i))) :
    Function.Injective (trialAddress B leaf n x t) := by
  intro i j h
  have hl : leaf i = leaf j := congrArg Sigma.fst h
  have hc : child i = child j := hbranch i j hl
  have hv := congrArg (fun z : GridAddress B => z.2.val) h
  change (dyadicKey (B (leaf i)) _).val = (dyadicKey (B (leaf j)) _).val at hv
  rw [hl] at hv
  have hk : dyadicKey (B (leaf j)) (x + t * (2 : ℝ)⁻¹ ^ n i) =
      dyadicKey (B (leaf j)) (x + t * (2 : ℝ)⁻¹ ^ n j) := Fin.ext hv
  have hcoarse := dyadicKey_eq_of_refine (hrefine j) hk
  have hi : n i ≤ b (child j) := hc ▸ hnhi i
  have hn : n i = n j :=
    dyadicKey_injOn (a := 3) (by omega) htlo hthi
      ⟨hnlo i, hi⟩ ⟨hnlo j, hnhi j⟩ hcoarse
  exact hpair (Prod.ext hc hn)

/-- A uniform block of `r` indices for each of `M` nondefault children.
This finite trial type has exactly the exponent used in the miss formula. -/
abbrev WindowTrial (M r : ℕ) := Fin M × Fin r

def windowTrialIndex {M r : ℕ} (a : Fin M → ℕ) (i : WindowTrial M r) : ℕ :=
  a i.1 + i.2.val

@[simp] theorem card_windowTrial (M r : ℕ) :
    Fintype.card (WindowTrial M r) = M * r := by simp [WindowTrial]

theorem windowTrialIndex_bounds {M r : ℕ} (a : Fin M → ℕ)
    (ha : ∀ i, 3 ≤ a i) (i : WindowTrial M r) :
    3 ≤ windowTrialIndex a i ∧ windowTrialIndex a i ≤ a i.1 + r - 1 := by
  have h := i.2.isLt
  have h' := ha i.1
  dsimp [windowTrialIndex]
  omega

theorem windowTrial_pair_injective {M r : ℕ} {E : Type u_E}
    (a : Fin M → ℕ) (edge : Fin M → E) (hedge : Function.Injective edge) :
    Function.Injective (fun i : WindowTrial M r =>
      (edge i.1, windowTrialIndex a i)) := by
  intro i j h
  have hc : i.1 = j.1 := hedge (congrArg Prod.fst h)
  have hn : windowTrialIndex a i = windowTrialIndex a j := congrArg Prod.snd h
  have ho : i.2 = j.2 := by
    apply Fin.ext
    dsimp [windowTrialIndex] at hn
    rw [hc] at hn
    omega
  exact Prod.ext hc ho

end Problem310.TrialAddresses

end

end OAI
