import OAI.MeasureTheory.Falconer.Estimates.RegularClasses

namespace OAI

/-! # Actual descendant counts for a single regularized profile -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem RegularizedProfileData.cell_mass_upper {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X : CellPath d) (hX : X.length = a) :
    (ρ (Q.descendant X).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N)) := by
  by_cases hp : 0 < ρ (Q.descendant X).carrier
  · exact (h.cells a ha X hX hp).2.trans_eq
      (Real.rpow_add (by positivity) _ _).symm
  · have hz : ρ (Q.descendant X).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

theorem RegularizedProfileData.descendant_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X : CellPath d) (hX : X.length = a) :
    (((Q.descendant X).occupiedPaths ρ (p-a)).card : ℝ) ≤
      ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) := by
  let := h.probability
  let R := (2:ℝ)^N
  let ℓ := ((d:ℝ)+1)*lam
  let lo := R^(-ℓ-m ((p:ℝ)/N))
  let S := (Q.descendant X).occupiedPaths ρ (p-a)
  have hlo : 0 < lo := by dsimp [lo,R]; positivity
  have hmass (z : CellPath d) (hz : z ∈ S) :
      lo ≤ (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    have hz' : z ∈ cubePaths d (p-a) ∧
        0 < ρ ((Q.descendant X).descendant z).carrier := by
      simpa only [S,DyadicCube.occupiedPaths,Finset.mem_filter] using hz
    obtain ⟨hz,hpos⟩ := hz'
    have hlen : (X++z).length = p := by
      simp only [List.length_append,hX,(mem_cubePaths _ _ _).mp hz]
      omega
    have hh := (h.cells p hp (X++z) hlen
      (by simpa only [Q.descendant_append] using hpos)).1
    simpa only [Q.descendant_append,lo,R,ℓ,sub_eq_add_neg,neg_mul,
      Real.rpow_add (by positivity : 0 < (2:ℝ)^N)] using hh
  have he : ρ (Q.descendant X).carrier =
      ∑ z ∈ S, ρ ((Q.descendant X).descendant z).carrier := by
    have hh := congrArg (fun ν : Measure (Space d) => ν univ)
      ((Q.descendant X).restrict_occupiedPaths ρ (p-a))
    simpa only [Measure.restrict_apply_univ,Measure.finsetSum_apply,S] using hh
  have hr : (ρ (Q.descendant X).carrier).toReal =
      ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    rw [he,ENNReal.toReal_sum]
    intro z _
    exact measure_ne_top ρ _
  have hc : (S.card:ℝ)*lo ≤ R^(ℓ-m ((a:ℝ)/N)) := by
    calc
      _ = ∑ _z ∈ S, lo := by simp
      _ ≤ ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal :=
        Finset.sum_le_sum hmass
      _ = (ρ (Q.descendant X).carrier).toReal := hr.symm
      _ ≤ _ := h.cell_mass_upper (hap.trans hp) X hX
  apply (le_div_iff₀ hlo).mpr at hc
  apply hc.trans_eq
  dsimp only [lo,R,ℓ]
  rw [← Real.rpow_sub (by positivity)]
  congr 1
  ring

theorem RegularizedProfileData.pair_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : CellPath d) (hX : X.length = a) (hY : Y.length = a) :
    ((((Q.descendant X).occupiedPaths ρ (p-a)) ×ˢ
      ((Q.descendant Y).occupiedPaths ρ (p-a))).card : ℝ) ≤
      ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) *
        ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) :=
      mul_le_mul (h.descendant_count hap hp X hX) (h.descendant_count hap hp Y hY)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem RegularizedProfileData.pair_count_two {Q₁ Q₂ : DyadicCube d}
    {ρ₁ ρ₂ : Measure (Space d)} {N : ℕ} {s₁ s₂ lam : ℝ} {m₁ m₂ : ℝ → ℝ}
    (h₁ : RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁)
    (h₂ : RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : CellPath d) (hX : X.length = a) (hY : Y.length = a) :
    ((((Q₁.descendant X).occupiedPaths ρ₁ (p-a)) ×ˢ
      ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))).card : ℝ) ≤
      ((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+
        (m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ ((2:ℝ)^N)^(m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) *
        ((2:ℝ)^N)^(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) :=
      mul_le_mul (h₁.descendant_count hap hp X hX) (h₂.descendant_count hap hp Y hY)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer.Regularization

end OAI
