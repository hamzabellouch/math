import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCoarseFeatures

namespace OAI

/-! # Exact finite-feature form of a coarse kernel -/

namespace JointDickman
open Finset

noncomputable def groupedKernelCoefficient {D R : Type*} [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) (d e : D) : ℝ :=
  δ^2*∑ r, ∑ s, K (d,r) (e,s)

theorem groupedKernelBilinear_eq {D R : Type*} [Fintype D] [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) (u v : D → ℝ) :
    finiteKernelBilinear (fun _ => δ) K (fun a => u a.1) (fun a => v a.1) =
      ∑ d, ∑ e, groupedKernelCoefficient δ K d e*u d*v e := by
  simp only [finiteKernelBilinear,finiteKernelAction,Fintype.sum_prod_type,
    groupedKernelCoefficient,mul_sum,sum_mul]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  ring

noncomputable def primeCoarseCoefficient (m B : ℕ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    Fin m → Fin m → ℝ :=
  groupedKernelCoefficient (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))

noncomputable def primeCoarseKernel (m B : ℕ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (x y : auxiliaryPrimes B → Bool) : ℝ :=
  ∑ d, ∑ e, primeCoarseCoefficient m B K d e*
    primeCoarseFeature m B d x*primeCoarseFeature m B e y

theorem coarseLogMassBilinear_features {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      ∑ d, ∑ e, primeCoarseCoefficient m B K d e*
        (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B d x)*
        (∑ y, fullPrimeMass (auxiliaryPrimes B) y*h y*primeCoarseFeature m B e y) := by
  rw [coarseLogMassBilinear_reindex]
  rw [funext (fun a => groupedManuscriptChannel_coarse_feature hm hB g a),
    funext (fun a => groupedManuscriptChannel_coarse_feature hm hB h a)]
  exact groupedKernelBilinear_eq (D := Fin m) (R := Fin (channelBlockCount m B))
    (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
    (fun d => ∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B d x)
    (fun e => ∑ y, fullPrimeMass (auxiliaryPrimes B) y*h y*primeCoarseFeature m B e y)

theorem sum_four_comm {X Y D E : Type*} [Fintype X] [Fintype Y] [Fintype D] [Fintype E]
    (f : X → Y → D → E → ℝ) :
    (∑ x, ∑ y, ∑ d, ∑ e, f x y d e) = ∑ d, ∑ e, ∑ x, ∑ y, f x y d e := by
  calc
    _ = ∑ x, ∑ d, ∑ y, ∑ e, f x y d e := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ d, ∑ x, ∑ y, ∑ e, f x y d e := sum_comm
    _ = ∑ d, ∑ x, ∑ e, ∑ y, f x y d e := by
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]

theorem primeCoarseKernel_test (m B : ℕ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
      g x*h y*primeCoarseKernel m B K x y) =
      ∑ d, ∑ e, primeCoarseCoefficient m B K d e*
        (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x*primeCoarseFeature m B d x)*
        (∑ y, fullPrimeMass (auxiliaryPrimes B) y*h y*primeCoarseFeature m B e y) := by
  simp only [primeCoarseKernel,mul_sum,sum_mul]
  rw [sum_four_comm]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

theorem coarseLogMassBilinear_eq_kernel_test {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      ∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
        g x*h y*primeCoarseKernel m B K x y := by
  rw [coarseLogMassBilinear_features hm hB,primeCoarseKernel_test]

end JointDickman

end OAI
