import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstRoughScales

namespace OAI

/-! In the new middle range, the distinguished coordinates themselves
are the shorter group. Their fixed exponent gap supplies the full
bilinear length conditions without a configuration-dependent choice. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def distinguishedCoordinateSet (i j : ℕ) : Finset (Fin i ⊕ Fin j) :=
  Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩

lemma distinguishedCoordinateSet_scale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ) :
    largeTupleSubsetScale k (distinguishedCoordinateSet i j) = largeTupleDistinguishedScale k := by
  simp only [largeTupleSubsetScale,distinguishedCoordinateSet,Finset.prod_map,
    Function.Embedding.coeFn_mk,largeTupleDistinguishedScale]

lemma distinguishedCoordinateSet_nonempty {i j : ℕ} {X : ℝ} (hX : 1 < X)
    (k : (Fin i ⊕ Fin j) → ℕ)
    (hh : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale k) :
    (distinguishedCoordinateSet i j).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hs := distinguishedCoordinateSet_scale k
  rw [he,largeTupleSubsetScale,Finset.prod_empty] at hs
  rw [←hs] at hh
  exact (not_le_of_gt (Real.one_lt_rpow hX (by norm_num : (0:ℝ) < 69/200))) hh

theorem eventually_scaleFirst_middle_range (i j : ℕ) {η : ℝ} (hη : 0 < η) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H : ℝ) {N : ℕ}
      (k : (Fin i ⊕ Fin j) → Fin N),
      X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      largeTupleDistinguishedScale (fun a => (k a).val) < X^(38/100:ℝ) →
      ∀ q : (Fin i → Eisenstein) × (Fin j → Eisenstein),
      uncutPrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
      let B := largeTupleSubsetScale (fun a => (k a).val) (distinguishedCoordinateSet i j)
      let A := largeTupleSubsetScale (fun a => (k a).val)
        (Finset.univ\distinguishedCoordinateSet i j)
      X^(1/3:ℝ) ≤ B ∧ A*B ≤ 3*X ∧
        B^(1-η/16) ≤ A ∧ A ≤ B^2/(1+Real.log B)^G := by
  have hδ : (0:ℝ) < 69/200-1/3 := by norm_num
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_prime_box_range hδ hη (i+j) G] with X hX hrange
  intro ℓ ξ Ct H N k hhigh hlow q hne
  let s := distinguishedCoordinateSet i j
  let B := largeTupleSubsetScale (fun a => (k a).val) s
  let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
  have hB : B = largeTupleDistinguishedScale (fun a => (k a).val) :=
    distinguishedCoordinateSet_scale _
  have hBp : 0 < B := largeTupleSubsetScale_pos _ _
  have hBX : X^(1/3+(69/200-1/3):ℝ) ≤ B := by
    rw [show (1/3:ℝ)+(69/200-1/3) = 69/200 by ring,hB]
    exact hhigh
  have hsq : B^2 ≤ 3*X := by
    have hb : B ≤ X^(38/100:ℝ) := by rw [hB]; exact hlow.le
    have hh := pow_le_pow_left₀ hBp.le hb 2
    have he : (X^(38/100:ℝ))^2 = X^(76/100:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ X)]
      norm_num
    rw [he] at hh
    exact (hh.trans (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (76/100:ℝ) ≤ 1))).trans
      (by rw [Real.rpow_one]; linarith)
  have hp : A*B = largeTupleSubsetScale (fun a => (k a).val) Finset.univ := by
    dsimp only [A,B]
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hprod := scaleFirstPrimeTuplePiece_scale_product (zero_lt_one.trans_le hX) k hne
  rw [←hp] at hprod
  obtain ⟨hlo,hhi⟩ := hrange A B hprod.1 hprod.2 hsq hBX
  exact ⟨(Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/3:ℝ) ≤ 69/200)).trans
    (by rw [←hB] at hhigh; exact hhigh),hprod.2,hlo,hhi⟩

end CubicFirstMoment

end

end OAI
