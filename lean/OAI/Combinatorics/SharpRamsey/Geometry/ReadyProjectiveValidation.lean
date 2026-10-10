import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.GeometricInduction

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in

lemma trimmed_sparse (S : Finset (Projectivization K V))
    (T T' : Finset (Projectivization K (Module.Dual K V))) (hT : T'⊆T)
    (C : ℝ) (hC : 0<C) (htrim : (T.card:ℝ)≤2*T'.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20000*C*Nat.card K)) :
    (incidenceCount S T':ℝ)≤(S.card:ℝ)*T'.card/(10000*C*Nat.card K) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos : 0<Nat.card K)
  have hi : incidenceCount S T'≤ incidenceCount S T := by
    apply sum_le_sum_of_subset_of_nonneg hT
    intros
    exact Nat.zero_le _
  apply (show (incidenceCount S T':ℝ)≤ incidenceCount S T by exact_mod_cast hi).trans
  apply hsparse.trans
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htrim (Nat.cast_nonneg S.card))
    (show 0≤20000*C*(Nat.card K:ℝ) by positivity)
  convert hh using 1; ring

theorem scheduled_from_original {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S X W : Finset (Projectivization K V)) (hS : S.Nonempty) (hX : X.Nonempty)
    (hXS : X⊆S) (hXW : X⊆W)
    (T T' U : Finset (Projectivization K (Module.Dual K V))) (hT' : T'.Nonempty)
    (hT'T : T'⊆T) (hT'U : T'⊆U) (htrim : (T.card:ℝ)≤2*T'.card)
    (C a : ℝ) (hC : 1≤C) (hcap : (S.card:ℝ)≤C*X.card)
    (hratio : (W.card:ℝ)≤exp a*X.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20000*C*Nat.card K)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card T'.card
    let m := scheduleCutoff q a h
    let M := 1000*C*q^(n+3)/S.card
    let accept := implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident q U T' M)
    (9/10:ℝ)≤prob (uniformMass X) h (GoodCap SharpLogRamsey.Incidence.Incident q U T' M) ∧
    1-PublicTables.integral (rowLaw W (hX.mono hXW) h) accept (fun _ => 1) m≤exp (-q) ∧
    (∀ y,PublicTables.integral (rowLaw W (hX.mono hXW) h) accept
      (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m≤
        6*C*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)) := by
  exact scheduled_validation hdim S X W hS hX hXS hXW T' U hT' hT'U C a hC hcap hratio
    (trimmed_sparse S T T' hT'T C (by linarith) htrim hsparse)

variable [Fintype I]

theorem scheduled_ready_exclusion {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : PublicTables.Law I) (Ready : I→Prop)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (T : Finset (Projectivization K (Module.Dual K V)))
    (X W : I→Finset (Projectivization K V))
    (T' U : I→Finset (Projectivization K (Module.Dual K V)))
    (hX : ∀ i,(X i).Nonempty) (hXW : ∀ i,X i⊆W i)
    (hXS : ∀ i,Ready i→X i⊆S)
    (hT' : ∀ i,Ready i→(T' i).Nonempty)
    (hT'T : ∀ i,Ready i→T' i⊆T) (hT'U : ∀ i,Ready i→T' i⊆U i)
    (htrim : ∀ i,Ready i→(T.card:ℝ)≤2*(T' i).card)
    (C : ℝ) (a : I→ℝ) (hC : 1≤C)
    (hcap : ∀ i,Ready i→(S.card:ℝ)≤C*(X i).card)
    (hratio : ∀ i,Ready i→((W i).card:ℝ)≤exp (a i)*(X i).card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20000*C*Nat.card K))
    (y : Projectivization K (Module.Dual K V)) :
    let q : ℝ := Nat.card K
    let h i := scheduleLength q (U i).card (T' i).card
    let m i := scheduleCutoff q (a i) (h i)
    let M := 1000*C*q^(n+3)/S.card
    (∑ i, if Ready i then p.mass i *
      PublicTables.integral (rowLaw (W i) ((hX i).mono (hXW i)) (h i))
        (implementAccept (X i) (GoodCap SharpLogRamsey.Incidence.Incident q (U i) (T' i) M))
        (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) (m i) else 0) ≤
      6*C*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x) := by
  dsimp only
  let B := 6*C*(Nat.card K:ℝ)*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)
  have hB : 0≤B := by
    dsimp [B]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _ => uniform_nonneg S x)
  calc
    _ ≤ ∑ i,p.mass i*B := by
      apply sum_le_sum
      intro i _
      by_cases hi : Ready i
      · rw [ite_eq_left hi]
        apply mul_le_mul_of_nonneg_left _ (p.nonneg i)
        exact (scheduled_from_original hdim S (X i) (W i) hS (hX i) (hXS i hi) (hXW i)
          T (T' i) (U i) (hT' i hi) (hT'T i hi) (hT'U i hi) (htrim i hi)
          C (a i) hC (hcap i hi) (hratio i hi) hsparse).2.2 y
      · rw [ite_eq_right hi]
        exact mul_nonneg (p.nonneg i) hB
    _ = _ := by rw [←sum_mul,p.total,one_mul]

end
end SharpLogRamsey.Validation

end

end OAI
