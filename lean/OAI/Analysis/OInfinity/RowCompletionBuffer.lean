import OAI.Analysis.OInfinity.RowCompletionBase

namespace OAI

/-! # Completions in the first buffer commutant

The relative path data records the fixed complement at every time. The
second buffer is constructed by the explicit central-row theorem inside
the norm ultrapower; its target family consists of elements of the first
buffer commutant. No commuting-row existence is assumed.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

local instance rowCompletionCentralizerClosed (R : ℕ → E) :
    IsClosed (StarSubalgebra.centralizer ℂ (Set.range R) : Set E) :=
  Set.isClosed_centralizer _

structure RelativeBinaryCompletion {n : ℕ} (q : E) (b : Fin 2 → E)
    (x : Fin (n + 1) → E) where
  row : Fin 2 → E
  implementer : unitary E
  deformation : Path (1 : unitary E) implementer
  fixes_complement : ∀ t, (deformation t : E) * (1 - q) = 1 - q ∧
    (1 - q) * (deformation t : E) = 1 - q
  support : ∀ i, q * row i = row i ∧ row i * q = row i
  gram : ∀ i j, star (row i) * row j = if i = j then q else 0
  range_sum : (∑ i, row i * star (row i)) = q
  encoded_prefix : ∀ i : Fin (n + 1), row 0 ^ (i : ℕ) * row 1 = x i
  cocycle : ∀ j, (implementer : E) * row j = b j

/-- A relative completion whose whole connecting path fixes the external
complement, obtained by doing the three connected moves in the corner. -/
lemma exists_relative_connected_binary_completion {n : ℕ}
    (q : E) (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (x : Fin (n + 2) → E)
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (b : Fin 2 → E)
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (hbs : (∑ i, b i * star (b i)) = q)
    (r : Fin 3 → E)
    (hrs : ∀ i, q * r i = r i ∧ r i * q = r i)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (her : Commute (star (r 0)) (x (Fin.last (n + 1))))
    (hfr : Commute (star (r 1)) (b 0 * x (Fin.last (n + 1)))) :
    Nonempty (RelativeBinaryCompletion q b (fun i : Fin (n + 1) => x i.castSucc)) := by
  let : NeZero q := ⟨hq0⟩
  let H := ProjectionCorner q hq hqq
  let f := projectionCornerInclusion q hq hqq
  have hf1 : f 1 = q := rfl
  have hfa (a : H) : f a = (a : E) := rfl
  have hbsup (i : Fin 2) : q * b i = b i ∧ b i * q = b i :=
    ⟨finiteRow_left_support q b hq hqq hb hbs i,
      finiteRow_right_support q b hq hqq hb i⟩
  let X : Fin (n + 2) → H := fun i => projectionCornerElement q hq hqq (x i) (hxs i)
  let B : Fin 2 → H := fun i => projectionCornerElement q hq hqq (b i) (hbsup i)
  let R : Fin 3 → H := fun i => projectionCornerElement q hq hqq (r i) (hrs i)
  have hX := projectionCornerElement_gram q hq hqq x hxs hx
  have hB := projectionCornerElement_gram q hq hqq b hbsup hb
  have hBs := projectionCornerElement_range_sum q hq hqq b hbsup hbs
  have hR := projectionCornerElement_gram q hq hqq r hrs hr
  have he : star (X (Fin.last (n + 1))) * X (Fin.last (n + 1)) = 1 := by
    simpa only [ite_true] using hX (Fin.last (n + 1)) (Fin.last (n + 1))
  have hxe (i : Fin (n + 1)) : star (X i.castSucc) * X (Fin.last (n + 1)) = 0 := by
    have hne : i.castSucc ≠ Fin.last (n + 1) := by
      intro h
      have hh := congrArg Fin.val h
      change (i : ℕ) = n + 1 at hh
      omega
    simpa only [hne, ite_false] using hX i.castSucc (Fin.last (n + 1))
  obtain ⟨a, u, hu, hag, has, ha, huc⟩ := exists_connected_binary_row_completion
    (fun i : Fin (n + 1) => X i.castSucc)
    (fun i j => by simpa only [Fin.castSucc_inj] using hX i.castSucc j.castSucc)
    (X (Fin.last (n + 1))) he hxe B hB hBs R hR
    (show Commute (star (R 0)) (X (Fin.last (n + 1))) from Subtype.ext her.eq)
    (show Commute (star (R 1)) (B 0 * X (Fin.last (n + 1))) from Subtype.ext hfr.eq)
  let p := hu.somePath
  let U := projectionCornerUnitary q hq hqq u
  let P : Path (1 : unitary E) U :=
    { toFun := fun t => projectionCornerUnitary q hq hqq (p t)
      continuous_toFun := (projectionCornerUnitary_continuous q hq hqq).comp p.continuous
      source' := by rw [p.source, projectionCornerUnitary_one]
      target' := by rw [p.target] }
  refine ⟨{
    row := fun i => f (a i)
    implementer := U
    deformation := P
    fixes_complement := fun t => projectionCornerUnitary_complement q hq hqq (p t)
    support := fun i => (a i).property
    gram := ?_
    range_sum := ?_
    encoded_prefix := ?_
    cocycle := ?_ }⟩
  · intro i j
    have h := congrArg f (hag i j)
    by_cases hij : i = j
    · simpa only [hij, ite_true, map_mul, map_star, hf1] using h
    · simpa only [hij, ite_false, map_mul, map_star, map_zero] using h
  · have h := congrArg f has
    simpa only [map_sum, map_mul, map_star, hf1] using h
  · intro i
    have h := congrArg f (ha i)
    rw [nonunital_map_pow_mul] at h
    exact h
  · intro j
    change ((((u : H) : E) + (1 - q)) * f (a j)) = b j
    rw [add_mul, sub_mul, one_mul, hfa, (a j).property.1, sub_self, add_zero]
    exact congrArg f (huc j)

/-- Diagonalizing an element of the first row commutant preserves that
membership in the next norm ultrapower. -/
def rowCentralizerDiagonalHom (U : Ultrafilter ℕ) (R : ℕ → E) :
    StarSubalgebra.centralizer ℂ (Set.range R) →⋆ₐ[ℂ]
      StarSubalgebra.centralizer ℂ
        (Set.range (fun i => NormUltra.QuotientAlgebra.diagonalHom U (R i))) := by
  let C := StarSubalgebra.centralizer ℂ (Set.range R)
  let D := StarSubalgebra.centralizer ℂ
    (Set.range (fun i => NormUltra.QuotientAlgebra.diagonalHom U (R i)))
  let d := NormUltra.QuotientAlgebra.diagonalHom (A := E) U
  refine (d.comp C.subtype).codRestrict D ?_
  intro x
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨h₁, h₂⟩ := (StarSubalgebra.mem_centralizer_iff ℂ).mp x.property (R i) ⟨i, rfl⟩
  constructor
  · change d (R i) * d (x : E) = d (x : E) * d (R i)
    simpa only [map_mul] using congrArg d h₁
  · change star (d (R i)) * d (x : E) = d (x : E) * star (d (R i))
    simpa only [map_mul, map_star] using congrArg d h₂

/-- The second proper row is actually built. Its entries remain in the
first row's commutant and commute with every member of the chosen target
family and its adjoint. -/
lemma exists_normUltrapower_row_in_commutant [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)] (R : ℕ → E)
    (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (t : ℕ → StarSubalgebra.centralizer ℂ (Set.range R)) :
    ∃ z : ℕ → StarSubalgebra.centralizer ℂ
        (Set.range (fun i => NormUltra.QuotientAlgebra.diagonalHom U (R i))),
      (∀ i j, star (z i) * z j = if i = j then 1 else 0) ∧
      ∀ i j, Commute (z i) (rowCentralizerDiagonalHom U R (t j)) ∧
        Commute (z i) (star (rowCentralizerDiagonalHom U R (t j))) := by
  let T : ℕ → E := fun i => t i
  have hRT : bergRowsCommute R T := by
    intro i j
    obtain ⟨h₁, h₂⟩ := (StarSubalgebra.mem_centralizer_iff ℂ).mp (t j).property (R i) ⟨i, rfl⟩
    refine ⟨h₁, ?_⟩
    change R i * star (t j : E) = star (t j : E) * R i
    simpa only [star_mul, star_star] using (congrArg star h₂).symm
  obtain ⟨Z, hZ, hZR, hZT⟩ := exists_normUltrapower_central_cuntz_row U R T hR hRT
  have hmem (i : ℕ) : Z i ∈ StarSubalgebra.centralizer ℂ
      (Set.range (fun j => NormUltra.QuotientAlgebra.diagonalHom U (R j))) := by
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨(hZR i j).1.symm, (hZR i j).2.symm⟩
  let z i := (⟨Z i, hmem i⟩ : StarSubalgebra.centralizer ℂ
    (Set.range (fun j => NormUltra.QuotientAlgebra.diagonalHom U (R j))))
  refine ⟨z, ?_, fun i j => ?_⟩
  · intro i j
    apply Subtype.ext
    change star (Z i) * Z j = ↑(if i = j then (1 : StarSubalgebra.centralizer ℂ
      (Set.range (fun j => NormUltra.QuotientAlgebra.diagonalHom U (R j)))) else 0)
    split_ifs with hij
    · change star (Z i) * Z j = 1
      simpa only [hij, ite_true] using hZ i j
    · change star (Z i) * Z j = 0
      simpa only [hij, ite_false] using hZ i j
  · constructor
    · exact Subtype.ext (hZT i j).1.eq
    · exact Subtype.ext (hZT i j).2.eq

private lemma rowCentralizerDiagonal_norm (U : Ultrafilter ℕ) (R : ℕ → E)
    (x : StarSubalgebra.centralizer ℂ (Set.range R)) :
    ‖rowCentralizerDiagonalHom U R x‖ = ‖x‖ := by
  change ‖NormUltra.QuotientAlgebra.mk U (DirectComparison.boundedDiagonal (x : E))‖ = ‖(x : E)‖
  rw [NormUltra.QuotientAlgebra.norm_mk_eq_limsup]
  change Filter.limsup (fun _ : ℕ => ‖(x : E)‖) (U : Filter ℕ) = ‖(x : E)‖
  rw [Filter.limsup_const]

/-- The same reference completion is available for both proper finite
rows after the second, explicitly constructed buffer. All resulting data
belong to the first buffer commutant. -/
lemma exists_buffer_preserving_pair_completions [Nontrivial E]
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (R : ℕ → E) (hR : ∀ i j, star (R i) * R j = if i = j then 1 else 0)
    (q : StarSubalgebra.centralizer ℂ (Set.range R))
    (hq : star q = q) (hqq : q * q = q) (hq0 : q ≠ 0)
    (n : ℕ) (x y : Fin (n + 2) → StarSubalgebra.centralizer ℂ (Set.range R))
    (hxs : ∀ i, q * x i = x i ∧ x i * q = x i)
    (hys : ∀ i, q * y i = y i ∧ y i * q = y i)
    (hx : ∀ i j, star (x i) * x j = if i = j then q else 0)
    (hy : ∀ i j, star (y i) * y j = if i = j then q else 0)
    (b : Fin 2 → StarSubalgebra.centralizer ℂ (Set.range R))
    (hb : ∀ i j, star (b i) * b j = if i = j then q else 0)
    (hbs : (∑ i, b i * star (b i)) = q) :
    let θ := rowCentralizerDiagonalHom U R
    Nonempty (RelativeBinaryCompletion (θ q) (fun j => θ (b j))
      (fun i : Fin (n + 1) => θ (x i.castSucc))) ∧
    Nonempty (RelativeBinaryCompletion (θ q) (fun j => θ (b j))
      (fun i : Fin (n + 1) => θ (y i.castSucc))) := by
  intro θ
  let C := StarSubalgebra.centralizer ℂ (Set.range R)
  let D := StarSubalgebra.centralizer ℂ
    (Set.range (fun i => NormUltra.QuotientAlgebra.diagonalHom U (R i)))
  let ex := x (Fin.last (n + 1))
  let ey := y (Fin.last (n + 1))
  let t : ℕ → C := fun i => if i = 0 then q else if i = 1 then ex else
    if i = 2 then b 0 * ex else if i = 3 then ey else b 0 * ey
  obtain ⟨z, hz, hzt⟩ := exists_normUltrapower_row_in_commutant U R hR t
  have hzq (j : ℕ) : Commute (z j) (θ q) := by
    simpa only [t, ite_true] using (hzt j 0).1
  have hzex (j : ℕ) : Commute (star (z j)) (θ ex) := by
    have h := (hzt j 1).2.star_star
    simpa only [t, show (1 : ℕ) ≠ 0 by decide, ite_false, ite_true, star_star] using h
  have hzfx (j : ℕ) : Commute (star (z j)) (θ (b 0 * ex)) := by
    have h := (hzt j 2).2.star_star
    simpa only [t, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      ite_false, ite_true, star_star] using h
  have hzey (j : ℕ) : Commute (star (z j)) (θ ey) := by
    have h := (hzt j 3).2.star_star
    simpa only [t, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ite_false, ite_true, star_star] using h
  have hzfy (j : ℕ) : Commute (star (z j)) (θ (b 0 * ey)) := by
    have h := (hzt j 4).2.star_star
    simpa only [t, show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
      show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ite_false, star_star] using h
  have hqD : star (θ q) = θ q := by rw [← map_star, hq]
  have hqqD : θ q * θ q = θ q := by rw [← map_mul, hqq]
  have hqD0 : θ q ≠ 0 := by
    intro hzero
    have hn := rowCentralizerDiagonal_norm U R q
    change ‖θ q‖ = ‖q‖ at hn
    rw [hzero, norm_zero] at hn
    exact hq0 (norm_eq_zero.mp hn.symm)
  have map_support (a : Fin (n + 2) → C) (hs : ∀ i, q * a i = a i ∧ a i * q = a i) :
      ∀ i, θ q * θ (a i) = θ (a i) ∧ θ (a i) * θ q = θ (a i) := by
    intro i
    constructor
    · simpa only [map_mul] using congrArg θ (hs i).1
    · simpa only [map_mul] using congrArg θ (hs i).2
  have map_gram {I : Type} [DecidableEq I] (a : I → C)
      (h : ∀ i j, star (a i) * a j = if i = j then q else 0) :
      ∀ i j, star (θ (a i)) * θ (a j) = if i = j then θ q else 0 := by
    intro i j
    rw [← map_star, ← map_mul, h]
    split_ifs <;> simp only [map_zero]
  have hbsD : (∑ i, θ (b i) * star (θ (b i))) = θ q := by
    simpa only [map_sum, map_mul, map_star] using congrArg θ hbs
  let r : Fin 3 → D := fun i => z i * θ q
  have hrs (i : Fin 3) : θ q * r i = r i ∧ r i * θ q = r i := by
    constructor
    · change θ q * (z i * θ q) = z i * θ q
      rw [← mul_assoc, ← (hzq i).eq, mul_assoc, hqqD]
    · change (z i * θ q) * θ q = z i * θ q
      rw [mul_assoc, hqqD]
  have hrg (i j : Fin 3) : star (r i) * r j = if i = j then θ q else 0 := by
    change star (z i * θ q) * (z j * θ q) = _
    rw [star_mul, hqD]
    calc
      _ = θ q * (star (z i) * z j) * θ q := by noncomm_ring
      _ = _ := by
        rw [hz]
        by_cases hij : i = j
        · simpa only [hij, ite_true, mul_one] using hqqD
        · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
          simp only [hne, hij, ite_false, mul_zero, zero_mul]
  have q_commutes (a : C) (ha : q * a = a ∧ a * q = a) : Commute (θ q) (θ a) := by
    change θ q * θ a = θ a * θ q
    rw [← map_mul, ← map_mul, ha.1, ha.2]
  have q_bex : q * (b 0 * ex) = b 0 * ex ∧ (b 0 * ex) * q = b 0 * ex := by
    constructor
    · rw [← mul_assoc, finiteRow_left_support q b hq hqq hb hbs 0]
    · rw [mul_assoc, (hxs (Fin.last (n + 1))).2]
  have q_bey : q * (b 0 * ey) = b 0 * ey ∧ (b 0 * ey) * q = b 0 * ey := by
    constructor
    · rw [← mul_assoc, finiteRow_left_support q b hq hqq hb hbs 0]
    · rw [mul_assoc, (hys (Fin.last (n + 1))).2]
  have hrex : Commute (star (r 0)) (θ ex) := by
    change Commute (star (z 0 * θ q)) (θ ex)
    rw [star_mul, hqD]
    exact (q_commutes ex (hxs _)).mul_left (hzex 0)
  have hrfx : Commute (star (r 1)) (θ (b 0) * θ ex) := by
    rw [← map_mul]
    change Commute (star (z 1 * θ q)) (θ (b 0 * ex))
    rw [star_mul, hqD]
    exact (q_commutes (b 0 * ex) q_bex).mul_left (hzfx 1)
  have hrey : Commute (star (r 0)) (θ ey) := by
    change Commute (star (z 0 * θ q)) (θ ey)
    rw [star_mul, hqD]
    exact (q_commutes ey (hys _)).mul_left (hzey 0)
  have hrfy : Commute (star (r 1)) (θ (b 0) * θ ey) := by
    rw [← map_mul]
    change Commute (star (z 1 * θ q)) (θ (b 0 * ey))
    rw [star_mul, hqD]
    exact (q_commutes (b 0 * ey) q_bey).mul_left (hzfy 1)
  exact ⟨exists_relative_connected_binary_completion (θ q) hqD hqqD hqD0
      (fun i => θ (x i)) (map_support x hxs) (map_gram (I := Fin (n + 2)) x hx)
      (fun j => θ (b j)) (map_gram (I := Fin 2) b hb) hbsD r hrs hrg hrex hrfx,
    exists_relative_connected_binary_completion (θ q) hqD hqqD hqD0
      (fun i => θ (y i)) (map_support y hys) (map_gram (I := Fin (n + 2)) y hy)
      (fun j => θ (b j)) (map_gram (I := Fin 2) b hb) hbsD r hrs hrg hrey hrfy⟩

end WeakPureInfiniteness

end

end OAI
