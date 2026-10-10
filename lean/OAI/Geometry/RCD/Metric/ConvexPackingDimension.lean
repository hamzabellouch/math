import OAI.Geometry.RCD.Metric.ConvexPackingGrid

namespace OAI

/-! # Exact packing growth excludes an extra independent convex direction -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_packing_no_extra_direction {K : Set E} (hK : Convex ℝ K) (h0 : 0 ∈ K)
    (n : ℕ) (M : ℝ)
    (hpack : ∀ {ι : Type} [Fintype ι] (v : ι → E) {d : ℝ}, 0 < d → d ≤ 1 →
      (∀ i, v i ∈ K) → Pairwise (fun i j => d ≤ dist (v i) (v j)) →
      (Fintype.card ι:ℝ)*(d/2)^n ≤ M)
    (v : Fin (n+1) → E) (hv : ∀ i, v i ∈ K) : ¬LinearIndependent ℝ v := by
  intro hlin
  obtain ⟨C,hC,hsep⟩ := convexGridPoint_separated (by omega : 0<n+1) v hlin
  have hm : (0:ℝ) < n+1 := by positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (max (max 1 (1/(C*(n+1)))) (M*(2*C*(n+1))^n))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hN)
  have hNpos : 0 < N := by exact_mod_cast (lt_trans zero_lt_one hN1)
  have hNinv : 1/(C*(n+1)) < N := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hN)
  have hNbound : M*(2*C*(n+1))^n < N := (le_max_right _ _).trans_lt hN
  let d := 1/(C*N*(n+1))
  have hd : 0<d := by dsimp only [d]; positivity
  have hd1 : d≤1 := by
    have hc := (div_lt_iff₀ (mul_pos hC hm)).mp hNinv
    dsimp only [d]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hp := hpack (fun j : Fin (n+1) → Fin N => convexGridPoint v j) hd hd1
    (fun j => convexGridPoint_mem hK h0 (by omega) hNpos v hv j) (fun i j hij => by
      simpa only [d,Nat.cast_add,Nat.cast_one] using hsep N hNpos i j hij)
  have hcard : (Fintype.card (Fin (n+1) → Fin N):ℝ) = (N:ℝ)^(n+1) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  rw [hcard] at hp
  have he : (N:ℝ)^(n+1)*(d/2)^n = (N:ℝ)/(2*C*(n+1))^n := by
    have hscale : d/2 = (1/(2*C*(n+1)))/(N:ℝ) := by
      dsimp only [d]
      field_simp
    rw [hscale,div_pow,one_div_pow,pow_succ]
    field_simp
  rw [he] at hp
  have hle := (div_le_iff₀ (pow_pos (by positivity : (0:ℝ)<2*C*(n+1)) n)).mp hp
  exact (not_le_of_gt hNbound) hle

end RegularPointCoordinates

end

end OAI
