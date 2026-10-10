import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ReadyProjectiveValidation

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]

lemma integral_finset_sum (p : Law Ω) (A : Ω→Prop) (f : Y→Ω→ℝ) (s : Finset Y) (m : ℕ) :
    integral p A (fun z => ∑ y∈s,f y z) m = ∑ y∈s,integral p A (f y) m := by
  have ho (z : Table Ω m) : outcome A (fun z => ∑ y∈s,f y z) m z=
      ∑ y∈s,outcome A (f y) m z := by
    unfold outcome
    cases first A m z <;> simp
  simp only [integral,ho,mul_sum]
  exact sum_comm

lemma integral_div (p : Law Ω) (A : Ω→Prop) (f : Ω→ℝ) (b : ℝ) (m : ℕ) :
    integral p A (fun z => f z/b) m=integral p A f m/b := by
  have ho (z : Table Ω m) : outcome A (fun z => f z/b) m z=outcome A f m z/b := by
    unfold outcome
    cases first A m z <;> simp
  simp only [integral,ho,←mul_div_assoc,←sum_div]

end
end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def excludedFraction {Ω Y : Type*} [Fintype Ω] (R : Ω→Y→Prop) (q : ℝ) (Y₀ : Finset Y)
    {h : ℕ} (z : Fin h→Ω) : ℝ :=
  ((Y₀.filter (fun y => ¬pass R q z y)).card:ℝ)/Y₀.card

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in

theorem produced_support_loss {h m : ℕ}
    (p : PublicTables.Law (Fin h→Projectivization K V))
    (accept : (Fin h→Projectivization K V)→Prop)
    (S : Finset (Projectivization K V))
    (Y : Finset (Projectivization K (Module.Dual K V))) (B q : ℝ)
    (hy : ∀ y,PublicTables.integral p accept (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m≤
      B*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)) :
    PublicTables.integral p accept (excludedFraction SharpLogRamsey.Incidence.Incident q Y) m≤
      B*(incidenceCount S Y:ℝ)/((S.card:ℝ)*Y.card) := by
  have he (z : Fin h→Projectivization K V) :
      excludedFraction SharpLogRamsey.Incidence.Incident q Y z=(∑ y∈Y,if ¬pass SharpLogRamsey.Incidence.Incident q z y then (1:ℝ) else 0)/(Y.card:ℝ) := by
    simp only [excludedFraction,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [funext he]
  rw [PublicTables.integral_div,PublicTables.integral_finset_sum]
  have hh := sum_le_sum (fun y (_ : y∈Y) => hy y)
  rw [←mul_sum,uniform_incidence_sum] at hh
  simpa only [←mul_div_assoc,div_div] using
    div_le_div_of_nonneg_right hh (Nat.cast_nonneg Y.card)

theorem scheduled_support_loss {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S X W : Finset (Projectivization K V)) (hS : S.Nonempty) (hX : X.Nonempty)
    (hXS : X⊆S) (hXW : X⊆W)
    (T T' U : Finset (Projectivization K (Module.Dual K V))) (hT' : T'.Nonempty)
    (hT'T : T'⊆T) (hT'U : T'⊆U) (htrim : (T.card:ℝ)≤2*T'.card)
    (C a : ℝ) (hC : 1≤C) (hcap : (S.card:ℝ)≤C*X.card)
    (hratio : (W.card:ℝ)≤exp a*X.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20000*C*Nat.card K))
    (Y : Finset (Projectivization K (Module.Dual K V))) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card T'.card
    let m := scheduleCutoff q a h
    let M := 1000*C*q^(n+3)/S.card
    let accept := implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident q U T' M)
    PublicTables.integral (rowLaw W (hX.mono hXW) h) accept
      (excludedFraction SharpLogRamsey.Incidence.Incident q Y) m≤
      (6*C*q)*(incidenceCount S Y:ℝ)/((S.card:ℝ)*Y.card) := by
  apply produced_support_loss
  exact (scheduled_from_original hdim S X W hS hX hXS hXW T T' U hT' hT'T hT'U htrim
    C a hC hcap hratio hsparse).2.2

end
end SharpLogRamsey.Validation

end

end OAI
