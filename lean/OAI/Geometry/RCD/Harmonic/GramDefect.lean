import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # A single nonnegative defect for the finite harmonic coordinate family -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def gramDefect {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (x : X) : ℝ :=
  ∑ i, ∑ j, |localGamma μ hQ (u i) (u j) x - (if i=j then 1 else 0)|

theorem gramDefect_nonneg {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (x : X) :
    0 ≤ gramDefect μ hQ u x :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem gramDefect_entry_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (i j : Fin n) (x : X) :
    |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ≤ gramDefect μ hQ u x := by
  have hinner : |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ≤
      ∑ k : Fin n, |localGamma μ hQ (u i) (u k) x-(if i=k then 1 else 0)| :=
    Finset.single_le_sum (fun k _ => abs_nonneg
      (localGamma μ hQ (u i) (u k) x-(if i=k then 1 else 0))) (Finset.mem_univ j)
  apply hinner.trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ =>
    abs_nonneg (localGamma μ hQ (u k) (u l) x-(if k=l then 1 else 0)))) (Finset.mem_univ i)

theorem gramDefect_integrableOn {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    {Ω : Set X} (hΩ : μ Ω ≠ ⊤) : IntegrableOn (gramDefect μ hQ u) Ω μ := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub
    (integrableOn_const (C := (if i=j then (1:ℝ) else 0)) hΩ)).abs

theorem gramDefect_integral_bound
    {n : ℕ} {p : X} {R ε : ℝ} {u : Fin n → SobolevSpace μ hQ} {v : X → Euclidean n}
    (hvol : 0 < μ.real (ball p R)) (hfin : μ (ball p R) ≠ ⊤)
    (hsplit : FirstOrderSplittingOn μ hQ p R ε u v) :
    (∫ x in ball p R, gramDefect μ hQ u x ∂μ) ≤ (n:ℝ)^2*ε*μ.real (ball p R) := by
  have hint (i j : Fin n) : IntegrableOn
      (fun x => |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)|) (ball p R) μ :=
    ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub (integrableOn_const hfin)).abs
  have hb (i j : Fin n) : (∫ x in ball p R,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ) ≤ ε*μ.real (ball p R) := by
    have hh := hsplit.gram i j
    rw [← div_eq_inv_mul,div_le_iff₀ hvol] at hh
    exact hh
  unfold gramDefect
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j)]
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε*μ.real (ball p R) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end RegularPointCoordinates

end

end OAI
