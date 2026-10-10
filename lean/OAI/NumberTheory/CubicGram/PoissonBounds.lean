import Mathlib
import OAI.NumberTheory.CubicGram.SieveBase
import OAI.NumberTheory.CubicGram.SieveExponent

namespace OAI

/-! Poisson numerical estimates and local-to-global sieve bounds. -/

section

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma poisson_power_identity {z n : ℝ} (hz : 0 < z) (hn : 0 < n) (r : ℝ) :
    (z/n)*(27*n^2/z)^r = 27^r*z^(1-r)*n^(2*r-1) := by
  rw [Real.div_rpow (by positivity) hz.le,Real.mul_rpow (by norm_num) (by positivity),
    Real.rpow_sub hz,Real.rpow_one,Real.rpow_sub hn,Real.rpow_one,
    Real.rpow_mul hn.le]
  norm_num only [Real.rpow_two]
  ring

lemma dual_length_neg_power {z n : ℝ} (hz : 0 < z) (hn : 0 < n) (r : ℝ) :
    (z/(27*n^2))^(-r) = (27*n^2/z)^r := by
  rw [Real.rpow_neg (by positivity),← Real.inv_rpow (by positivity)]
  congr 1
  field_simp

lemma poisson_cross_one {z n : ℝ} (hz : 0 < z) (hn : 0 < n) :
    (z/n)*(2*n)*(27*n^2/z)^(1/3 : ℝ) ≤ 6*(z*n)^(2/3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (z/n)*(2*n)*(27*n^2/z)^(1/3 : ℝ))
    (by positivity : 0 ≤ 6*(z*n)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
  simp only [mul_pow]
  rw [rpow_third_cube (by positivity),rpow_two_thirds_cube (by positivity)]
  field_simp
  nlinarith

lemma poisson_cross_two {z n : ℝ} (hz : 0 < z) (hn : 0 < n) (hnz : n ≤ z) :
    (z/n)*(2*n)^(2/3 : ℝ)*(27*n^2/z)^(2/3 : ℝ) ≤ 54*(z*n)^(2/3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (z/n)*(2*n)^(2/3 : ℝ)*(27*n^2/z)^(2/3 : ℝ))
    (by positivity : 0 ≤ 54*(z*n)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
  simp only [mul_pow]
  rw [rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity),
    rpow_two_thirds_cube (by positivity)]
  have hne := mul_le_mul_of_nonneg_left hnz (by positivity : 0 ≤ z*n^2)
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hnz (by positivity : 0 ≤ z*n^2)]

lemma poisson_dual_numerical {ξ δ z n : ℝ} (_hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n) (hnz : n ≤ z) :
    (z/n)*(2*n)^δ*
      ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+
       (2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
       (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1))) ≤
       (54000 : ℝ)*(z*n)^δ*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hz : 0 < z := hn0.trans_le hnz
  let t : ℝ := 27*n^2/z
  have ht : 0 < t := by dsimp [t]; positivity
  have heps : (2*n*t)^δ ≤ 54*(z*n)^δ := by
    have hlen : 2*n*t ≤ 54*(z*n) := by
      dsimp [t]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hz).mpr
      nlinarith [sq_le_sq₀ hn0.le hz.le |>.mpr hnz]
    calc
      _ ≤ (54*(z*n))^δ := Real.rpow_le_rpow (by positivity) hlen hδ.le
      _ = 54^δ*(z*n)^δ := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 54*(z*n)^δ := by
        have hh : (54 : ℝ)^δ ≤ 54 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 54) hδ1
        gcongr
  have h1 : (z/n)*((2*n)*t^(1/3 : ℝ)) ≤ 6*(z*n)^(2/3 : ℝ) := by
    simpa only [← mul_assoc] using poisson_cross_one hz hn0
  have h2 : (z/n)*((2*n)^(2/3 : ℝ)*t^(2/3 : ℝ)) ≤ 54*(z*n)^(2/3 : ℝ) := by
    simpa only [← mul_assoc] using poisson_cross_two hz hn0 hnz
  have hx : (z/n)*t^ξ ≤ 729*(z^(1-ξ)*n^(2*ξ-1)) := by
    rw [poisson_power_identity hz hn0]
    have hp : (27 : ℝ)^ξ ≤ 729 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 27) hξ2
      norm_num at hh ⊢
      exact hh
    calc
      _ = 27^ξ*(z^(1-ξ)*n^(2*ξ-1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hlast : (z/n)*t = 27*n := by dsimp [t]; field_simp
  have hsum : (z/n)*((2*n)*t^(1/3 : ℝ)+(2*n)^(2/3 : ℝ)*t^(2/3 : ℝ)+t^ξ+t) ≤
      1000*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1)) := by
    have hnon : 0 ≤ (z*n)^(2/3 : ℝ) := by positivity
    have hnon' : 0 ≤ z^(1-ξ)*n^(2*ξ-1) := by positivity
    nlinarith
  have hexpand : (z/n)*(2*n)^δ*
      ((2*n)*(z/(27*n^2))^(-(δ+1/3 : ℝ))+
       (2*n)^(2/3 : ℝ)*(z/(27*n^2))^(-(δ+2/3 : ℝ))+
       (z/(27*n^2))^(-(δ+ξ))+(z/(27*n^2))^(-(δ+1))) =
      (2*n*t)^δ*((z/n)*((2*n)*t^(1/3 : ℝ)+(2*n)^(2/3 : ℝ)*t^(2/3 : ℝ)+t^ξ+t)) := by
    simp only [dual_length_neg_power hz hn0,
      Real.mul_rpow (by positivity : 0 ≤ 2*n) ht.le]
    dsimp only [t]
    rw [Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_one]
    ring
  rw [hexpand]
  calc
    _ ≤ (54*(z*n)^δ)*(1000*((z*n)^(2/3 : ℝ)+n+z^(1-ξ)*n^(2*ξ-1))) :=
      mul_le_mul heps hsum (by positivity) (by positivity)
    _ = _ := by ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_split (S H : Finset Eisenstein) (p : Eisenstein → Prop)
    (hS : ∀ a ∈ S, primary a) (hH : ∀ b ∈ H, primary b) :
    finiteCubicBound S H ≤ finiteCubicBound (S.filter p) H +
      finiteCubicBound (S.filter (fun a => ¬p a)) H := by
  have he : S = (Finset.univ : Finset Bool).biUnion (fun b => S.filter (fun a => if b then p a else ¬p a)) := by
    ext a; simp; tauto
  rw [finiteCubicBound_symm S H hS hH]
  have hh := finiteCubicBound_biUnion (Finset.univ : Finset Bool) H
    (fun b => S.filter (fun a => if b then p a else ¬p a))
  rw [← he] at hh
  have ht := finiteCubicBound_symm H (S.filter p) hH (fun a ha => hS a (Finset.mem_filter.mp ha).1)
  have hf := finiteCubicBound_symm H (S.filter (fun a => ¬p a)) hH
    (fun a ha => hS a (Finset.mem_filter.mp ha).1)
  simpa [Fintype.sum_bool,ht,hf,add_comm] using hh

lemma finiteCubicBound_base_dyad (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ),
      0 < M → 0 < N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*N^ε*(M+N^2) := by
  obtain ⟨C,hC,hbound⟩ := finiteCubicBound_base_thin ε hε
  refine ⟨C+2*C*(Real.sqrt 2)^ε,by positivity,?_⟩
  intro S H M N hM hN hS hH
  let S₀ := S.filter (fun a => norm a ≤ Real.sqrt 2*N)
  let S₁ := S.filter (fun a => ¬norm a ≤ Real.sqrt 2*N)
  have hS₀ : ∀ a ∈ S₀, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N := by
    intro a ha; have hh := Finset.mem_filter.mp ha
    exact ⟨(hS a hh.1).1,(hS a hh.1).2.1,(hS a hh.1).2.2.1,hh.2⟩
  have hS₁ : ∀ a ∈ S₁, primary a ∧ Squarefree a ∧ Real.sqrt 2*N ≤ norm a ∧ norm a ≤ Real.sqrt 2*(Real.sqrt 2*N) := by
    intro a ha; have hh := Finset.mem_filter.mp ha
    refine ⟨(hS a hh.1).1,(hS a hh.1).2.1,le_of_not_ge hh.2,?_⟩
    have he : Real.sqrt 2*(Real.sqrt 2*N) = 2*N := by rw [← mul_assoc,Real.mul_self_sqrt (by norm_num)]
    rw [he]; exact (hS a hh.1).2.2.2
  have h0 := hbound S₀ H M N hM hN hS₀ hH
  have h1 := hbound S₁ H M (Real.sqrt 2*N) hM (by positivity) hS₁ hH
  have hsq : (Real.sqrt 2*N)^2 = 2*N^2 := by rw [mul_pow,Real.sq_sqrt (by norm_num)]
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hN.le,hsq] at h1
  have hsplit := finiteCubicBound_split S H (fun a => norm a ≤ Real.sqrt 2*N)
    (fun a ha => (hS a ha).1) (fun x hx => (hH x hx).1)
  have hnon : 0 ≤ C*(Real.sqrt 2)^ε*N^ε*M := by positivity
  dsimp only [S₀,S₁] at h0 h1
  nlinarith

lemma finiteCubicBound_base_global (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ),
      1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*N^ε*(M+N^2) := by
  obtain ⟨C,hC,hbound⟩ := finiteCubicBound_base_dyad (ε/2) (by linarith)
  obtain ⟨D,hD,hpoly⟩ := dyadic_polynomial_small_power 1 (show 0 < ε/2 by linarith)
  refine ⟨C*D,by positivity,?_⟩
  intro S H M N hM hN hS hH
  let L := Nat.log 2 ⌊N⌋₊
  let R : ℕ → Finset Eisenstein := fun j => S.filter (fun a => Nat.log 2 (normNat a) = j)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hfloor : ⌊N⌋₊ ≠ 0 := by
    have hh : (1 : ℕ) ≤ ⌊N⌋₊ := by apply Nat.le_floor; simpa using hN
    omega
  have hpow : (2 : ℝ)^L ≤ N := by
    have h := Nat.pow_log_le_self 2 hfloor
    have hr : (2 : ℝ)^L ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast h
    exact hr.trans (Nat.floor_le hN0.le)
  have hcover : S ⊆ (Finset.range (L+1)).biUnion R := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 (normNat a),Finset.mem_range.mpr ?_,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
    have hn : normNat a ≤ ⌊N⌋₊ := Nat.le_floor (by rw [normNat_cast]; exact (hS a ha).2.2)
    have hl : Nat.log 2 (normNat a) ≤ L := Nat.log_mono_right hn
    omega
  have hR (j : ℕ) : ∀ a ∈ R j, primary a ∧ Squarefree a ∧ (2 : ℝ)^j ≤ norm a ∧ norm a ≤ 2*(2 : ℝ)^j := by
    intro a ha
    have hh := Finset.mem_filter.mp ha
    have hfreq := frequencyDyad_norm (mem_frequencyDyad.mpr ⟨primary_ne_zero (hS a hh.1).1,hh.2⟩)
    exact ⟨(hS a hh.1).1,(hS a hh.1).2.1,hfreq⟩
  have hterm (j : ℕ) (hj : j ∈ Finset.range (L+1)) :
      finiteCubicBound H (R j) ≤ C*N^(ε/2)*(M+N^2) := by
    rw [finiteCubicBound_symm H _ (fun x hx => (hH x hx).1) (fun a ha => (hR j a ha).1)]
    apply (hbound (R j) H M ((2 : ℝ)^j) hM0 (by positivity) (hR j) hH).trans
    have hjL : j ≤ L := by have : j < L+1 := Finset.mem_range.mp hj; omega
    have hpowj : (2 : ℝ)^j ≤ N := (pow_le_pow_right₀ (by norm_num) hjL).trans hpow
    gcongr
  have hcount : (L+1 : ℝ) ≤ D*N^(ε/2) := by
    have hh := hpoly L
    simp only [pow_one] at hh
    have hp : D*((2 : ℝ)^L)^(ε/2) ≤ D*N^(ε/2) := by gcongr
    linarith
  calc
    _ = finiteCubicBound H S := finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun x hx => (hH x hx).1)
    _ ≤ finiteCubicBound H ((Finset.range (L+1)).biUnion R) := finiteCubicBound_mono (Finset.Subset.refl H) hcover
    _ ≤ ∑ j ∈ Finset.range (L+1), finiteCubicBound H (R j) := finiteCubicBound_biUnion _ _ _
    _ ≤ (L+1 : ℝ)*(C*N^(ε/2)*(M+N^2)) := by
      have h := Finset.sum_le_card_nsmul _ _ _ hterm
      simpa only [Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using h
    _ ≤ (D*N^(ε/2))*(C*N^(ε/2)*(M+N^2)) := by gcongr
    _ = C*D*N^ε*(M+N^2) := by
      have he : N^(ε/2)*N^(ε/2) = N^ε := by rw [← Real.rpow_add hN0]; congr 1; ring
      calc
        _ = C*D*(N^(ε/2)*N^(ε/2))*(M+N^2) := by ring
        _ = _ := by rw [he]

theorem sieveExponent_two : SieveExponent 2 := by
  intro ε hε
  obtain ⟨C,hC,hbase⟩ := finiteCubicBound_base_global ε hε
  refine ⟨C,hC,?_⟩
  intro S H M N hM hN hS hH
  apply (hbase S H M N hM hN hS (fun x hx => ⟨(hH x hx).1,(hH x hx).2.2⟩)).trans
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have he : M+N^2 ≤ M+(M*N)^(2/3 : ℝ)+N^(2 : ℝ) := by
    rw [Real.rpow_two]
    have : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
    linarith
  have hn : N ≤ M*N := le_mul_of_one_le_left hN0 hM
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 hn hε.le) hC.le)
    he (by positivity) (by positivity)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_empty (H : Finset Eisenstein) : finiteCubicBound ∅ H = 0 := by
  apply le_antisymm _ (finiteCubicBound_nonneg _ _)
  apply (finiteCubicBound_le_iff _ _ (by norm_num : (0 : ℝ) ≤ 0)).mpr
  intro u
  simp

lemma finiteCubicBound_local_to_global (S H : Finset Eisenstein) (N F : ℝ)
    (hN : 1 ≤ N) (hF : 0 ≤ F)
    (hS : ∀ a ∈ S, primary a ∧ norm a ≤ N) (hH : ∀ x ∈ H, primary x)
    (hlocal : ∀ (R : Finset Eisenstein), R ⊆ S → ∀ n : ℝ, 1 ≤ n → n ≤ N →
      (∀ a ∈ R, n ≤ norm a ∧ norm a ≤ Real.sqrt 2*n) → finiteCubicBound R H ≤ F) :
      finiteCubicBound S H ≤ 2*((Nat.log 2 ⌊N⌋₊ : ℝ)+1)*F := by
  let L := Nat.log 2 ⌊N⌋₊
  let R : ℕ → Finset Eisenstein := fun j => S.filter (fun a => Nat.log 2 (normNat a) = j)
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hfloor : ⌊N⌋₊ ≠ 0 := by
    have hh : (1 : ℕ) ≤ ⌊N⌋₊ := by apply Nat.le_floor; simpa using hN
    omega
  have hpow : (2 : ℝ)^L ≤ N := by
    have h := Nat.pow_log_le_self 2 hfloor
    have hr : (2 : ℝ)^L ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast h
    exact hr.trans (Nat.floor_le hN0.le)
  have hcover : S ⊆ (Finset.range (L+1)).biUnion R := by
    intro a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 (normNat a),Finset.mem_range.mpr ?_,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
    have hn : normNat a ≤ ⌊N⌋₊ := Nat.le_floor (by rw [normNat_cast]; exact (hS a ha).2)
    have hl : Nat.log 2 (normNat a) ≤ L := Nat.log_mono_right hn
    omega
  have hR (j : ℕ) : ∀ a ∈ R j, (2 : ℝ)^j ≤ norm a ∧ norm a ≤ 2*(2 : ℝ)^j := by
    intro a ha
    have hh := Finset.mem_filter.mp ha
    exact frequencyDyad_norm (mem_frequencyDyad.mpr ⟨primary_ne_zero (hS a hh.1).1,hh.2⟩)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (L+1)) : finiteCubicBound H (R j) ≤ 2*F := by
    have hjL : j ≤ L := by have := Finset.mem_range.mp hj; omega
    have hpowj : (2 : ℝ)^j ≤ N := (pow_le_pow_right₀ (by norm_num) hjL).trans hpow
    have hprim : ∀ a ∈ R j, primary a := fun a ha => (hS a (Finset.mem_filter.mp ha).1).1
    rw [finiteCubicBound_symm H _ hH hprim]
    let A := (R j).filter (fun a => norm a ≤ Real.sqrt 2*(2 : ℝ)^j)
    let B := (R j).filter (fun a => ¬norm a ≤ Real.sqrt 2*(2 : ℝ)^j)
    have hAS : A ⊆ S := fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    have hBS : B ⊆ S := fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    have hA : finiteCubicBound A H ≤ F := hlocal A hAS ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num)) hpowj (fun a ha =>
        ⟨(hR j a (Finset.mem_filter.mp ha).1).1,(Finset.mem_filter.mp ha).2⟩)
    have hB : finiteCubicBound B H ≤ F := by
      by_cases hBN : Real.sqrt 2*(2 : ℝ)^j ≤ N
      · refine hlocal B hBS (Real.sqrt 2*(2 : ℝ)^j) ?_ hBN ?_
        · exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))
        · intro a ha
          have hh := Finset.mem_filter.mp ha
          refine ⟨le_of_not_ge hh.2,?_⟩
          rw [← mul_assoc,Real.mul_self_sqrt (by norm_num)]
          exact (hR j a hh.1).2
      · have he : B = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          have hlo := (Finset.mem_filter.mp ha).2
          have hhi := (hS a (hBS ha)).2
          exact hlo (hhi.trans (le_of_not_ge hBN))
        rw [he,finiteCubicBound_empty]
        exact hF
    have hh := finiteCubicBound_split (R j) H (fun a => norm a ≤ Real.sqrt 2*(2 : ℝ)^j) hprim hH
    change finiteCubicBound (R j) H ≤ finiteCubicBound A H+finiteCubicBound B H at hh
    linarith
  calc
    _ = finiteCubicBound H S := finiteCubicBound_symm S H (fun a ha => (hS a ha).1) hH
    _ ≤ finiteCubicBound H ((Finset.range (L+1)).biUnion R) := finiteCubicBound_mono (Finset.Subset.refl H) hcover
    _ ≤ ∑ j ∈ Finset.range (L+1), finiteCubicBound H (R j) := finiteCubicBound_biUnion _ _ _
    _ ≤ (L+1 : ℝ)*(2*F) := by
      have hh := Finset.sum_le_card_nsmul _ _ _ hterm
      simpa only [Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using hh
    _ = _ := by ring

lemma cutoff_log_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → (Nat.log 2 ⌊N⌋₊ : ℝ)+1 ≤ C*N^ε := by
  obtain ⟨C,hC,h⟩ := dyadic_polynomial_small_power 1 hε
  refine ⟨C,hC,?_⟩
  intro N hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hfloor : ⌊N⌋₊ ≠ 0 := by
    have hh : (1 : ℕ) ≤ ⌊N⌋₊ := by apply Nat.le_floor; simpa using hN
    omega
  have hpow : (2 : ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ N := by
    have hr : (2 : ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hfloor
    exact hr.trans (Nat.floor_le hN0.le)
  have hh := h (Nat.log 2 ⌊N⌋₊)
  simp only [pow_one] at hh
  have hp : C*((2 : ℝ)^(Nat.log 2 ⌊N⌋₊))^ε ≤ C*N^ε := by gcongr
  linarith

end CubicFirstMoment
end
end

end OAI
