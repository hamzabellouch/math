import OAI.Geometry.PeriodicTiling.ShiftMultiplicity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import OAI.Geometry.PeriodicTiling.ActivationTiles
import OAI.Geometry.PeriodicTiling.Dependence
import Mathlib.Logic.Equiv.Prod

namespace OAI

universe uα uJ uC uK uZ

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

def MixedDifferenceZero {a b : ℕ} (Q : ZMod a × ZMod b → ℤ) : Prop :=
  ∀ x y, Q (x, y) - Q (x - 1, y) - Q (x, y - 1) + Q (x - 1, y - 1) = 0

private theorem zmod_eq_zero_of_pred_invariant {n : ℕ} [NeZero n] {α : Type uα}
    (f : ZMod n → α) (hf : ∀ x, f x = f (x - 1)) (x : ZMod n) : f x = f 0 := by
  have hnat : ∀ m : ℕ, f (m : ZMod n) = f 0 := by
    intro m
    induction m with
    | zero => simp only [Nat.cast_zero]
    | succ m ih =>
        calc
          f ((m + 1 : ℕ) : ZMod n) = f (m : ZMod n) := by
            simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
              hf ((m : ZMod n) + 1)
          _ = f 0 := ih
  simpa only [ZMod.natCast_zmod_val] using hnat x.val

theorem mixedDifference_rectangle {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℤ) (hmixed : MixedDifferenceZero Q)
    (x x₀ : ZMod a) (y : ZMod b) :
    Q (x, y) - Q (x₀, y) = Q (x, 0) - Q (x₀, 0) := by
  have hfirst (z : ZMod a) :
      Q (z, y) - Q (z - 1, y) = Q (z, 0) - Q (z - 1, 0) := by
    apply zmod_eq_zero_of_pred_invariant
      (fun w : ZMod b => Q (z, w) - Q (z - 1, w))
    intro w
    have h := hmixed z w
    linarith only [h]
  have hrow (z : ZMod a) :
      Q (z, y) - Q (z, 0) = Q (0, y) - Q (0, 0) := by
    apply zmod_eq_zero_of_pred_invariant
      (fun w : ZMod a => Q (w, y) - Q (w, 0))
    intro w
    have h := hfirst w
    linarith only [h]
  linarith only [hrow x, hrow x₀]

theorem histogram_separable {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ)
    (hmixed : MixedDifferenceZero (fun z => (Q z : ℤ))) :
    ∃ u : ZMod a → ℕ, ∃ v : ZMod b → ℕ, ∀ x y, Q (x, y) = u x + v y := by
  classical
  obtain ⟨x₀, _hx₀, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (ZMod a)) (fun x => Q (x, 0)) Finset.univ_nonempty
  let u : ZMod a → ℕ := fun x => Q (x, 0) - Q (x₀, 0)
  let v : ZMod b → ℕ := fun y => Q (x₀, y)
  refine ⟨u, v, ?_⟩
  intro x y
  have hle : Q (x₀, 0) ≤ Q (x, 0) := hmin x (Finset.mem_univ x)
  have hrectangle := mixedDifference_rectangle
    (fun z => (Q z : ℤ)) hmixed x x₀ y
  dsimp [u, v]
  omega

theorem histogram_mass_eq {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ) (u : ZMod a → ℕ) (v : ZMod b → ℕ)
    (hsep : ∀ x y, Q (x, y) = u x + v y) :
    (∑ z, Q z) = b * (∑ x, u x) + a * (∑ y, v y) := by
  calc
    (∑ z, Q z) = ∑ x : ZMod a, ∑ y : ZMod b, (u x + v y) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hsep x y
    _ = b * (∑ x, u x) + a * (∑ y, v y) := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem histogram_mass_dvd {a b D : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ)
    (hmixed : MixedDifferenceZero (fun z => (Q z : ℤ)))
    (hmass : (∑ z, Q z) = D) (hlarge : D < b) : a ∣ D := by
  obtain ⟨u, v, hsep⟩ := histogram_separable Q hmixed
  have htotal : D = b * (∑ x, u x) + a * (∑ y, v y) := by
    rw [← hmass]
    exact histogram_mass_eq Q u v hsep
  have hu : (∑ x, u x) = 0 := by
    by_contra hne
    have hone : 1 ≤ ∑ x, u x := Nat.one_le_iff_ne_zero.mpr hne
    have hmul : b ≤ b * (∑ x, u x) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hone
    omega
  refine ⟨∑ y, v y, ?_⟩
  simpa only [hu, Nat.mul_zero, Nat.zero_add] using htotal

private theorem sum_histogram_corner {a b : ℕ} [NeZero a] [NeZero b]
    (f : ZMod a × ZMod b → ℤ) (x : ZMod a) (y : ZMod b) :
    (∑ e : ZMod a × ZMod b,
      ((if e.1 = x then (1 : ℤ) else 0) * (if e.2 = y then 1 else 0)) * f e) =
        f (x, y) := by
  classical
  have hterm (e : ZMod a × ZMod b) :
      ((if e.1 = x then (1 : ℤ) else 0) * (if e.2 = y then 1 else 0)) * f e =
        if e = (x, y) then f e else 0 := by
    rcases e with ⟨x', y'⟩
    by_cases hx : x' = x <;> by_cases hy : y' = y <;>
      simp [hx, hy, Prod.mk.injEq]
  simp_rw [hterm]
  simp

theorem sum_shiftOmega_mul {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℤ) (x : ZMod a) (y : ZMod b) :
    (∑ e : ZMod a × ZMod b, shiftOmega a b e * Q ((x, y) - e)) =
      Q (x, y) - Q (x - 1, y) - Q (x, y - 1) + Q (x - 1, y - 1) := by
  classical
  have hexpand (e : ZMod a × ZMod b) :
      shiftOmega a b e * Q ((x, y) - e) =
        ((if e.1 = 0 then (1 : ℤ) else 0) * (if e.2 = 0 then 1 else 0)) *
            Q ((x, y) - e) -
          ((if e.1 = 1 then (1 : ℤ) else 0) * (if e.2 = 0 then 1 else 0)) *
            Q ((x, y) - e) -
          ((if e.1 = 0 then (1 : ℤ) else 0) * (if e.2 = 1 then 1 else 0)) *
            Q ((x, y) - e) +
          ((if e.1 = 1 then (1 : ℤ) else 0) * (if e.2 = 1 then 1 else 0)) *
            Q ((x, y) - e) := by
    unfold shiftOmega
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [sum_histogram_corner, Prod.mk_sub_mk, sub_zero]

theorem mixedDifferenceZero_of_shift_sum {a b D : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (Q : ZMod a × ZMod b → ℕ)
    (hmass : (∑ z, Q z) = D)
    (hcoverage : ∀ c : ZMod a × ZMod b,
      (∑ δ : ShiftIndex a b, Q (c - shift a b δ)) = D) :
    MixedDifferenceZero (fun z => (Q z : ℤ)) := by
  classical
  intro x y
  have hcount :
      (∑ δ : ShiftIndex a b, (Q ((x, y) - shift a b δ) : ℤ)) = (D : ℤ) := by
    exact_mod_cast hcoverage (x, y)
  rw [sum_shift (fun e : ZMod a × ZMod b => (Q ((x, y) - e) : ℤ))] at hcount
  simp only [nsmul_eq_mul] at hcount
  simp_rw [shiftMultiplicity_cast ha hb] at hcount
  simp only [add_mul, one_mul, Finset.sum_add_distrib] at hcount
  have hbase : (∑ e : ZMod a × ZMod b, (Q ((x, y) - e) : ℤ)) = (D : ℤ) := by
    have hinv : Function.Involutive (fun e : ZMod a × ZMod b => (x, y) - e) :=
      fun e => sub_sub_cancel (x, y) e
    calc
      (∑ e : ZMod a × ZMod b, (Q ((x, y) - e) : ℤ)) = ∑ e, (Q e : ℤ) :=
        hinv.bijective.sum_comp (fun e => (Q e : ℤ))
      _ = (D : ℤ) := by exact_mod_cast hmass
  rw [hbase, sum_shiftOmega_mul (fun z => (Q z : ℤ)) x y] at hcount
  linarith only [hcount]

theorem histogram_mass_dvd_of_shift_sum {a b D : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (Q : ZMod a × ZMod b → ℕ)
    (hmass : (∑ z, Q z) = D) (hlarge : D < b)
    (hcoverage : ∀ c : ZMod a × ZMod b,
      (∑ δ : ShiftIndex a b, Q (c - shift a b δ)) = D) : a ∣ D :=
  histogram_mass_dvd Q (mixedDifferenceZero_of_shift_sum ha hb Q hmass hcoverage)
    hmass hlarge

theorem sum_firstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} [Fintype J] [Fintype C] [Fintype K] [DecidableEq C]
    (f : J → C × K) (hf : Function.Bijective f) (c : C) :
    (∑ j, if (f j).1 = c then (1 : ℕ) else 0) = Fintype.card K := by
  calc
    _ = ∑ z : C × K, if z.1 = c then (1 : ℕ) else 0 :=
      hf.sum_comp (fun z => if z.1 = c then (1 : ℕ) else 0)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      dsimp only
      simp only [Fintype.sum_ite_eq', Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Nat.cast_id]

theorem card_firstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} [Fintype J] [Fintype C] [Fintype K] [DecidableEq C]
    (f : J → C × K) (hf : Function.Bijective f) (c : C) :
    Fintype.card {j : J // (f j).1 = c} = Fintype.card K := by
  simpa only [Fintype.card_subtype, Finset.card_filter] using
    sum_firstCoordinate_of_bijective f hf c

theorem sum_firstFirstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} {Z : Type uZ}
    [Fintype J] [Fintype C] [Fintype K] [Fintype Z]
    [DecidableEq C] (f : J → (C × K) × Z) (hf : Function.Bijective f) (c : C) :
    (∑ j, if (f j).1.1 = c then (1 : ℕ) else 0) =
      Fintype.card K * Fintype.card Z := by
  have h := sum_firstCoordinate_of_bijective
    (fun j => Equiv.prodAssoc C K Z (f j))
    ((Equiv.prodAssoc C K Z).bijective.comp hf) c
  change (∑ j, if (f j).1.1 = c then (1 : ℕ) else 0) =
    Fintype.card (K × Z) at h
  simpa only [Fintype.card_prod] using h

theorem card_firstFirstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} {Z : Type uZ}
    [Fintype J] [Fintype C] [Fintype K] [Fintype Z]
    [DecidableEq C] (f : J → (C × K) × Z) (hf : Function.Bijective f) (c : C) :
    Fintype.card {j : J // (f j).1.1 = c} =
      Fintype.card K * Fintype.card Z := by
  simpa only [Fintype.card_subtype, Finset.card_filter] using
    sum_firstFirstCoordinate_of_bijective f hf c

def seedHistogram {p : ℕ} [NeZero p] {C : Type uC}
    (q : Residues p → C) (c : C) : ℕ := by
  classical
  exact Fintype.card {s : Residues p // q s = c}

theorem seedHistogram_eq_sum {p : ℕ} [NeZero p] {C : Type uC} [DecidableEq C]
    (q : Residues p → C) (c : C) :
    seedHistogram q c = ∑ s : Residues p, if q s = c then (1 : ℕ) else 0 := by
  simp only [seedHistogram, Fintype.card_subtype, Finset.card_filter]

theorem sum_seedHistogram {p : ℕ} [NeZero p] {C : Type uC} [Fintype C]
    (q : Residues p → C) : (∑ c, seedHistogram q c) = p ^ 4 := by
  classical
  calc
    (∑ c, seedHistogram q c) =
        Fintype.card (Σ c : C, {s : Residues p // q s = c}) := by
      simp only [Fintype.card_sigma, seedHistogram]
    _ = Fintype.card (Residues p) := Fintype.card_congr (Equiv.sigmaFiberEquiv q)
    _ = p ^ 4 := by
      simp only [Residues, Fintype.card_prod, ZMod.card]
      ring

theorem sum_seedHistogram_translate {p : ℕ} [NeZero p]
    {C : Type uC} [AddCommGroup C] [DecidableEq C]
    (q : Residues p → C) (s : Residues p) (e c : C) :
    (∑ τ : Residues p, if q (s - τ) + e = c then (1 : ℕ) else 0) =
      seedHistogram q (c - e) := by
  have hinv : Function.Involutive (fun τ : Residues p => s - τ) :=
    fun τ => sub_sub_cancel s τ
  rw [seedHistogram_eq_sum]
  simpa only [eq_sub_iff_add_eq] using
    hinv.bijective.sum_comp (fun τ => if q τ + e = c then (1 : ℕ) else 0)

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem ordinary_active_of_tile (o : Outputs E) (hdep : HasDependence E o)
    (n : Column p) (htile : Tiles (ordinaryActivationTile E n) (graph o)) :
    ∀ x, ∃ j, Active E o (.inl n) x j := by
  classical
  intro x
  by_contra hno
  obtain ⟨c₀, hc⟩ := (no_active_iff_constant E o (.inl n) x).mp
    (fun j hj => hno ⟨j, hj⟩)
  have hsource (j : ActivationIndex E (.inl n)) :
      o.c (ordinarySource E n (x, 0) j) (.inl n) = c₀ := by
    calc
      _ = usefulAt E o (.inl n) (ordinarySource E n (x, 0) j).1
          ((ordinarySource E n (x, 0) j).2 (.inl n)) :=
        usefulAt_factor E hdep _ _ _
      _ = usefulAt E o (.inl n) x
          ((ordinarySource E n (x, 0) j).2 (.inl n)) :=
        usefulAt_eq_of_lineValue_eq E hdep n (ordinarySource_lineValue E n (x, 0) j) _
      _ = c₀ := hc _
  have hmap (j : ActivationIndex E (.inl n)) :
      (ordinaryActivationMap E n o (x, 0) j).1 =
        c₀ + shift (E.a (.inl n)) (E.b (.inl n)) j.2 := by
    change o.c (ordinarySource E n (x, 0) j) (.inl n) + _ = _
    rw [hsource]
  have htwo : (∑ δ : ShiftIndex (E.a (.inl n)) (E.b (.inl n)),
      if shift (E.a (.inl n)) (E.b (.inl n)) δ = 0 then (1 : ℕ) else 0) = 2 := by
    calc
      _ = ∑ e : P E (.inl n), shiftMultiplicity (E.a (.inl n)) (E.b (.inl n)) e •
          (if e = 0 then (1 : ℕ) else 0) := sum_shift _
      _ = shiftMultiplicity (E.a (.inl n)) (E.b (.inl n)) (0 : P E (.inl n)) := by
        simp [mul_ite]
      _ = 2 := by
        change shiftMultiplicity (E.a (.inl n)) (E.b (.inl n)) (0, 0) = 2
        exact shiftMultiplicity_zero
  have hcount := sum_firstCoordinate_of_bijective
    (ordinaryActivationMap E n o (x, 0))
    ((ordinaryActivationTile_iff E n o).mp htile (x, 0)) c₀
  simp_rw [hmap, add_eq_left] at hcount
  rw [Fintype.sum_prod_type] at hcount
  have hbad : E.r (.inl n) * 2 = E.r (.inl n) := by
    simpa only [htwo, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, K, ZMod.card]
      using hcount
  have hr := E.r_pos (.inl n)
  omega

theorem seed_active_somewhere_of_tile (o : Outputs E) (hdep : HasDependence E o)
    (t : Fin 2) (htile : Tiles (seedActivationTile E t) (graph o)) :
    ∃ x, Active E o (.inr t) x () := by
  classical
  by_contra hno
  have hinactive (x : Plane) : ¬ Active E o (.inr t) x () :=
    fun hx => hno ⟨x, hx⟩
  let q : Residues p → P E (.inr t) := fun s => seedFactor E o t s 0
  have hconstant (s : Residues p) (w : K E (.inr t)) :
      seedFactor E o t s w = q s := by
    obtain ⟨c, hc⟩ := (no_active_iff_constant E o (.inr t)
      (seedRepresentative p s)).mp (by
        intro j
        cases j
        exact hinactive (seedRepresentative p s))
    exact (hc w).trans (hc 0).symm
  have hfactor (x : Plane) (k : Input E) :
      o.c (x, k) (.inr t) = q (seedResidue p x) :=
    (seedFactor_spec E hdep t x k).trans (hconstant _ _)
  let b₀ : Base E := (0, 0)
  have hmap (j : SeedActivationIndex E t) :
      (seedActivationMap E t o b₀ j).1.1 =
        q (seedResidue p b₀.1 - j.2) +
          shift (E.a (.inr t)) (E.b (.inr t)) j.1.2 := by
    have hf := hfactor (seedSource E t b₀ j).1 (seedSource E t b₀ j).2
    change o.c (seedSource E t b₀ j) (.inr t) = _ at hf
    change o.c (seedSource E t b₀ j) (.inr t) + _ = _
    rw [hf]
    have hs : seedResidue p (seedSource E t b₀ j).1 =
        seedResidue p b₀.1 - j.2 := seedSource_residue E t b₀ j
    rw [hs]
  have hcoverage (c : P E (.inr t)) :
      (∑ δ : ShiftIndex (E.a (.inr t)) (E.b (.inr t)),
        seedHistogram q (c - shift (E.a (.inr t)) (E.b (.inr t)) δ)) = D p := by
    have hcount := sum_firstFirstCoordinate_of_bijective
      (seedActivationMap E t o b₀) ((seedActivationTile_iff E t o).mp htile b₀) c
    simp_rw [hmap] at hcount
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hcount
    simp_rw [sum_seedHistogram_translate] at hcount
    have hmul : E.r (.inr t) *
        (∑ δ : ShiftIndex (E.a (.inr t)) (E.b (.inr t)),
          seedHistogram q (c - shift (E.a (.inr t)) (E.b (.inr t)) δ)) =
        E.r (.inr t) * D p := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, K, ZMod.card]
        using hcount
    exact Nat.eq_of_mul_eq_mul_left (E.r_pos (.inr t)) hmul
  have hdiv : E.a (.inr t) ∣ p ^ 4 :=
    histogram_mass_dvd_of_shift_sum (E.a_two_le (.inr t)) (E.b_two_le (.inr t))
      (seedHistogram q) (sum_seedHistogram q) (E.seed_b_large t) hcoverage
  exact E.prime_ne_p (.inl (.inr t))
    (Nat.prime_eq_prime_of_dvd_pow (E.a_prime (.inr t)) E.p_prime hdiv)

end PeriodicTilingThree

end

end OAI
