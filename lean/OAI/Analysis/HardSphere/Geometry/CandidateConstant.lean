import Mathlib
import OAI.Analysis.HardSphere.Geometry.EnnrealTsumFinset
import OAI.Analysis.HardSphere.Geometry.NominalDrift

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

lemma geometricEnvelope_ne_top (A R : ℕ) (b q : ℝ≥0∞) (hb : b≠⊤) (hq : q<1)
    (z : ℤ×ℤ) : radiusEnvelope (geometricRadiusWeights A R b q) z≠⊤ := by
  rw [geometricRadiusWeights_envelope]
  apply ENNReal.add_ne_top.mpr
  constructor
  · split_ifs <;> simp_all
  · apply ne_top_of_le_ne_top (b:=∑' m : ℕ, q^(m+1))
    · have he : (∑' m : ℕ, q^(m+1))=q*(∑' m : ℕ,q^m) := by
        simp_rw [pow_succ',ENNReal.tsum_mul_left]
      rw [he,ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top (ne_of_lt (hq.trans (by norm_num)))
        (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hq)))
    · exact ENNReal.tsum_le_tsum fun m ↦ by split_ifs <;> simp

def candidateConstant (a : ℕ) : ℕ := (2*(a+3)+1)^3*2^((2*a+1)^3)+(12*a+24)

def encounterConstant (R : ℕ) : ℕ := 343*(2*R+1)^3

lemma candidateConstant_growth (a : ℕ) :
    (2*(a+3)+1)^3*2^((2*a+1)^3)≤candidateConstant a := Nat.le_add_right _ _

lemma candidateConstant_radius (a : ℕ) : 12*a+24≤candidateConstant a := Nat.le_add_left _ _

lemma encounterConstant_detour (R : ℕ) : 52*(2*R+1)^3≤encounterConstant R := by
  exact Nat.mul_le_mul_right _ (by norm_num)

theorem nominal_potential_bound {K m n : ℕ} [NeZero K] (R : ℕ)
    (hn : 0<n) (hnK : 2*n≤K) (ht : n/2≤3^m)
    (v : Vertex) (Δ₂ Δ₃ : ℤ) (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n)
    (w : FourNoise m) (κ t : ℝ) (hκ : 0≤κ) (ht0 : 0≤t)
    (hqt : (candidateConstant (R+2):ℝ)*t<1) :
    let U := nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w)
    let U' := nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w)
    let Γ := (nominalCover U).image (torusProjection K)
    let Γ' := (nominalCover U').image (torusProjection K)
    let weights := geometricRadiusWeights (candidateConstant (R+2)) (4*(R+6))
      (ENNReal.ofReal ((encounterConstant R:ℝ)*κ))
      (ENNReal.ofReal ((candidateConstant (R+2):ℝ)*t))
    κ*((encounterSet (torusNear K R) Γ Γ').card:ℝ)+
      (∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0) ≤
      ∑ j∈Finset.range (n+1), radiusPotential weights (differenceAt m (min j (n-j)) w) := by
  classical
  dsimp only
  let U := nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w)
  let U' := nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w)
  let Γ := (nominalCover U).image (torusProjection K)
  let Γ' := (nominalCover U').image (torusProjection K)
  let A := candidateConstant (R+2)
  let C := encounterConstant R
  let weights := geometricRadiusWeights A (4*(R+6)) (ENNReal.ofReal ((C:ℝ)*κ))
    (ENNReal.ofReal ((A:ℝ)*t))
  let z (i : Fin (n+1)) := differenceAt m (min i.val (n-i.val)) w
  have hspeed := nominal_speed m n hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ (secondPathNoise w)
  have hfirst := nominal_first m n v Δ₂ Δ₃ (firstPathNoise w)
  have hfirst' := nominal_first m n v Δ₂ Δ₃ (secondPathNoise w)
  have hnear (r : ℕ) (i : Fin (n+1)) :
      torusNear K r (torusProjection K (U i)) (torusProjection K (U' i)) ↔ z i∈square r :=
    nominal_near_iff m r hnK ht v Δ₂ Δ₃ w i
  have hN := nominal_encounter_bound R hnK U U' (v 0) hfirst hfirst' hspeed Γ Γ'
    (fun _ hx ↦ nominalCover_projection U hx) (fun _ hx ↦ nominalCover_projection U' hx)
  have hNen : ENNReal.ofReal (κ*((encounterSet (torusNear K R) Γ Γ').card:ℝ))≤
      ∑ i : Fin (n+1), if z i∈square (4*(R+6)) then ENNReal.ofReal ((C:ℝ)*κ) else 0 := by
    calc
      _ ≤ ENNReal.ofReal ((C:ℝ)*κ*
        ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
          (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have hN' : ((encounterSet (torusNear K R) Γ Γ').card:ℝ)≤
          (C:ℝ)*((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
            (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ) := by exact_mod_cast hN
        nlinarith
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hκ),ENNReal.ofReal_natCast]
        simp_rw [← hnear]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [mul_comm]
  have hF := contact_candidate_potential (R+2) hnK U U' (v 0) hfirst hfirst' hspeed Γ Γ'
    (fun _ hx ↦ nominalCover_projection U hx) (fun _ hx ↦ nominalCover_projection U' hx) (ENNReal.ofReal t)
  have hFen : ENNReal.ofReal (∑ F∈candidateSets (torusRangeGraph K (R+2)),
      if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0)≤
      ∑ i : Fin (n+1), ∑' l : ℕ, if z i∈square (A*(l+1))
        then (ENNReal.ofReal ((A:ℝ)*t))^(l+1) else 0 := by
    have hcast : ENNReal.ofReal (∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0)=
        ∑ F∈candidateSets (torusRangeGraph K (R+2)),
          if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (ENNReal.ofReal t)^F.card else 0 := by
      rw [ENNReal.ofReal_sum_of_nonneg (by intro F _; split_ifs <;> positivity)]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs <;> simp [ENNReal.ofReal_pow ht0]
    rw [hcast]
    refine hF.trans (Finset.sum_le_sum fun i _ ↦ ENNReal.tsum_le_tsum fun l ↦ ?_)
    by_cases h : torusNear K ((12*(R+2)+24)*(l+1)) (torusProjection K (U i)) (torusProjection K (U' i))
    · have hz : z i∈square (A*(l+1)) := (hnear _ i).mp
        (torusNear_mono (Nat.mul_le_mul_right _ (candidateConstant_radius (R+2))) h)
      rw [ite_eq_left h,ite_eq_left hz]
      apply pow_le_pow_left'
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
      apply mul_le_mul' _ le_rfl
      exact_mod_cast candidateConstant_growth (R+2)
    · rw [ite_eq_right h]; exact zero_le
  have hfinite (i : Fin (n+1)) : radiusEnvelope weights (z i)≠⊤ := by
    apply geometricEnvelope_ne_top _ _ _ _ ENNReal.ofReal_ne_top
    exact (ENNReal.ofReal_lt_one).mpr hqt
  have hbound := add_le_add hNen hFen
  rw [← Finset.sum_add_distrib] at hbound
  have hrw (i : Fin (n+1)) :
      (if z i∈square (4*(R+6)) then ENNReal.ofReal ((C:ℝ)*κ) else 0)+
      (∑' l : ℕ, if z i∈square (A*(l+1)) then (ENNReal.ofReal ((A:ℝ)*t))^(l+1) else 0)=
      ENNReal.ofReal (radiusPotential weights (z i)) := by
    rw [radiusPotential,ENNReal.ofReal_toReal (hfinite i)]
    exact (geometricRadiusWeights_envelope _ _ _ _ _).symm
  simp_rw [hrw] at hbound
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ radiusPotential_nonneg weights (z i))] at hbound
  rw [← ENNReal.ofReal_add (mul_nonneg hκ (Nat.cast_nonneg _))
    (Finset.sum_nonneg (by intro F _; split_ifs <;> positivity))] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg
    (fun i _ ↦ radiusPotential_nonneg weights (z i)))).mp hbound
  dsimp only [z] at hreal
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ radiusPotential weights (differenceAt m (min j (n-j)) w)) (n+1)] at hreal
  exact hreal

end HardSphere.Lattice

open scoped ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
omit [Fintype V] in

lemma prod_one_add_ofReal_le_exp_sum  {I : Type*} (Q : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ Q, 0 ≤ w i) :
    ∏ i ∈ Q, (1 + ENNReal.ofReal (w i)) ≤
      ENNReal.ofReal (Real.exp (∑ i ∈ Q, w i)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert i Q hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hwi := hw i (Finset.mem_insert_self i Q)
    have hQ : ∀ j ∈ Q, 0 ≤ w j := fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)
    apply mul_le_mul' _ (ih hQ)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hwi]
    exact ENNReal.ofReal_le_ofReal (by simpa [add_comm] using Real.add_one_le_exp (w i))

theorem badComponents_exponential_bound (G : SimpleGraph V)
    (μ : PMF (Finset V)) (p β : ℝ) (hp : 0 ≤ p)
    (hbad : JointBadLaw μ (ENNReal.ofReal p)) (P : Finset V → Prop) :
    (∑' B, μ B * ENNReal.ofReal (Real.exp
      (β * ∑ F∈badComponents G B, if P F then (F.card:ℝ) else 0))) ≤
      ENNReal.ofReal (Real.exp (∑ F∈candidateSets G,
        if P F then (p * Real.exp β)^F.card else 0)) := by
  let w : Finset V → ℝ≥0∞ := fun F ↦ if P F then
    ENNReal.ofReal (Real.exp (β * (F.card:ℝ))) else 0
  have hpoint (B : Finset V) :
      ENNReal.ofReal (Real.exp
        (β * ∑ F∈badComponents G B, if P F then (F.card:ℝ) else 0)) ≤
      ∏ F∈badComponents G B, (1+w F) := by
    rw [Finset.mul_sum, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    apply Finset.prod_le_prod
    intro F _
    by_cases h : P F
    · simp only [ite_eq_left h,w]
      exact le_add_self
    · simp only [ite_eq_right h,w,mul_zero,Real.exp_zero,ENNReal.ofReal_one,add_zero]
      exact le_rfl
  calc
    _ ≤ ∑' B, μ B * ∏ F∈badComponents G B, (1+w F) := by
      exact ENNReal.tsum_le_tsum fun B ↦ mul_le_mul' le_rfl (hpoint B)
    _ ≤ ∏ F∈candidateSets G, (1+(ENNReal.ofReal p)^F.card*w F) :=
      environment_product_bound μ _ hbad (badComponents G)
        (badComponents_disjoint G) (fun B F hF ↦ badComponents_subset G B hF)
        (candidateSets G) (badComponents_candidate G) w
    _ = ∏ F∈candidateSets G,
        (1+ENNReal.ofReal (if P F then (p*Real.exp β)^F.card else 0)) := by
      apply Finset.prod_congr rfl
      intro F _
      dsimp only [w]
      by_cases h : P F
      · simp only [ite_eq_left h]
        rw [← ENNReal.ofReal_pow hp,← ENNReal.ofReal_mul (pow_nonneg hp _),
          mul_comm β (F.card:ℝ),Real.exp_nat_mul,mul_pow]
      · simp only [ite_eq_right h,mul_zero,ENNReal.ofReal_zero]
    _ ≤ _ := prod_one_add_ofReal_le_exp_sum _ _ (by
      intro F _
      split_ifs
      · exact pow_nonneg (mul_nonneg hp (Real.exp_pos _).le) _
      · exact le_rfl)

end HardSphere.Lattice

end

end OAI
