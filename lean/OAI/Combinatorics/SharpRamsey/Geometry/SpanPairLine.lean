import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Weight
import OAI.Combinatorics.SharpRamsey.Geometry.VectorMap

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.ProjectiveLineChart
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
  SharpLogRamsey.RationalAffineChart
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}
lemma span_pair_of_line (W : Submodule K (Fin n → K)) (hW : Module.finrank K W = 2)
    (P Q : Projectivization K (Fin n → K)) (hPQ : P ≠ Q)
    (hP : P.submodule ≤ W) (hQ : Q.submodule ≤ W) :
    Submodule.span K {P.rep,Q.rep} = W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | rfl
    · apply hP
      rw [Projectivization.submodule_eq]
      exact Submodule.subset_span rfl
    · apply hQ
      rw [Projectivization.submodule_eq]
      exact Submodule.subset_span rfl
  · have hh := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hPQ)
    have he : Set.range ![P.rep,Q.rep] = {P.rep,Q.rep} := by
      ext v
      simp [or_comm]
    rw [he] at hh
    simpa [hW] using hh

lemma normalized_span (a : Fin n → E) (P Q : Projectivization K (Fin (n+1) → K))
    (hP : Avoids a P) (hQ : Avoids a Q) :
    Submodule.span E {lift a (coord a P),lift a (coord a Q)} =
      Submodule.span E {vectorMap (E := E) P.rep,vectorMap (E := E) Q.rep} := by
  have hp := congrArg Projectivization.submodule (mk_lift_chart a (pointMap P) hP)
  have hq := congrArg Projectivization.submodule (mk_lift_chart a (pointMap Q) hQ)
  rw [Projectivization.submodule_mk, map_submodule] at hp hq
  rw [show ({lift a (coord a P),lift a (coord a Q)} : Set _) =
    {lift a (coord a P)} ∪ {lift a (coord a Q)} by rfl]
  rw [Submodule.span_union, hp, hq, ← Submodule.span_union]
  rfl

theorem coord_mem_line (a : Fin n → E) (W : Submodule K (Fin (n+1) → K))
    (hW : Module.finrank K W = 2) (P Q R : Projectivization K (Fin (n+1) → K))
    (hPQ : P ≠ Q) (hP : P.submodule ≤ W) (hQ : Q.submodule ≤ W)
    (haP : Avoids a P) (haQ : Avoids a Q) (haR : Avoids a R) :
    R.submodule ≤ W ↔ ∃ t : E, coord a R = coord a P+t • (coord a Q-coord a P) := by
  rw [← lift_coord_mem a R haR W, ← span_pair_of_line W hW P Q hPQ hP hQ,
    extendSpace_span_pair, ← normalized_span a P Q haP haQ,
    lift_mem_span_pair]

lemma line_coord_ne (a : Fin n → E) (P Q : Projectivization K (Fin (n+1) → K))
    (haP : Avoids a P) (haQ : Avoids a Q) (hPQ : P ≠ Q) : coord a Q-coord a P ≠ 0 := by
  intro hh
  apply hPQ
  exact coord_injOn a haP haQ (sub_eq_zero.mp hh).symm

variable {ι : Type*}

theorem carriers_injective (a : Fin 3 → E) (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (P Q : ι → Projectivization K (Fin 4 → K))
    (hPQ : ∀ i, P i ≠ Q i) (hP : ∀ i, (P i).submodule ≤ W i)
    (hQ : ∀ i, (Q i).submodule ≤ W i)
    (haP : ∀ i, Avoids a (P i)) (haQ : ∀ i, Avoids a (Q i)) :
    Function.Injective (fun i => AffineIncidence.carrier (coord a (P i))
      (coord a (Q i)-coord a (P i))) := by
  intro i j hij
  dsimp only at hij
  apply hd
  have hm (R : Projectivization K (Fin 4 → K)) (haR : Avoids a R)
      (hr : R.submodule ≤ W i) : R.submodule ≤ W j := by
    have ht := (coord_mem_line a (W i) (hW i) (P i) (Q i) R
      (hPQ i) (hP i) (hQ i) (haP i) (haQ i) haR).mp hr
    have hh : coord a R ∈ AffineIncidence.carrier (coord a (P i))
        (coord a (Q i)-coord a (P i)) := by
      obtain ⟨t,ht⟩ := ht
      exact ⟨t,ht.symm⟩
    rw [hij] at hh
    apply (coord_mem_line a (W j) (hW j) (P j) (Q j) R
      (hPQ j) (hP j) (hQ j) (haP j) (haQ j) haR).mpr
    obtain ⟨t,ht⟩ := hh
    exact ⟨t,ht.symm⟩
  rw [← span_pair_of_line (W i) (hW i) (P i) (Q i) (hPQ i) (hP i) (hQ i)]
  exact span_pair_of_line (W j) (hW j) (P i) (Q i) (hPQ i)
    (hm _ (haP i) (hP i)) (hm _ (haQ i) (hQ i))

end
end SharpLogRamsey.ProjectiveLineChart
end

section

namespace SharpLogRamsey.RichProjectiveLines
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.ProjectiveBaseChange SharpLogRamsey.ProjectiveAffineChart
  SharpLogRamsey.RationalAffineChart SharpLogRamsey.ProjectiveLineChart
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
    [Infinite E] [IsAlgClosed E] [Fintype ι]

theorem card_lines_square
    (S : Finset (Projectivization K (Fin 4 → K)))
    (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (hM : ∀ i, 2 ≤ (S.filter (fun P => P.submodule ≤ W i)).card) :
    Fintype.card ι ≤ S.card^2 := by
  classical
  have htwo (i : ι) : ∃ P Q : Projectivization K (Fin 4 → K),
      P ∈ S ∧ Q ∈ S ∧ P.submodule ≤ W i ∧ Q.submodule ≤ W i ∧ P ≠ Q := by
    obtain ⟨P,hP,Q,hQ,hPQ⟩ := Finset.one_lt_card.mp (show
      1 < (S.filter (fun P => P.submodule ≤ W i)).card by have := hM i; omega)
    exact ⟨P,Q,(mem_filter.mp hP).1,(mem_filter.mp hQ).1,
      (mem_filter.mp hP).2,(mem_filter.mp hQ).2,hPQ⟩
  choose P Q hPS hQS hP hQ hPQ using htwo
  let f (i : ι) : S × S := (⟨P i,hPS i⟩,⟨Q i,hQS i⟩)
  have hf : Function.Injective f := by
    intro i j hij
    have hp : P i = P j := congrArg (fun x : S × S => x.1.val) hij
    have hq : Q i = Q j := congrArg (fun x : S × S => x.2.val) hij
    apply hd
    rw [← span_pair_of_line (W i) (hW i) (P i) (Q i) (hPQ i) (hP i) (hQ i),
      ← span_pair_of_line (W j) (hW j) (P j) (Q j) (hPQ j) (hP j) (hQ j),hp,hq]
  simpa only [Fintype.card_prod, Fintype.card_coe, pow_two] using
    Fintype.card_le_of_injective f hf

theorem card_mul_le {q : ℕ} [CharP E q] (h2 : (2:E) ≠ 0)
    (S : Finset (Projectivization K (Fin 4 → K))) (hS : S.Nonempty)
    (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (M Kp h C : ℕ) (hM2 : 2 ≤ M) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : ∀ i, M ≤ (S.filter (fun P => P.submodule ≤ W i)).card)
    (hcap : ∀ f : (Fin 4 → K) →ₗ[K] K, f ≠ 0 →
      (S.filter (fun P => f P.rep = 0)).card ≤ Kp)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (hsize : 2*p*S.card < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*S.card) :
    Fintype.card ι*M ≤ (6+72*C)*S.card := by
  classical
  obtain ⟨a,ha⟩ := RationalAffineChart.exists_avoiding (E := E) S
  have htwo (i : ι) : ∃ P Q : Projectivization K (Fin 4 → K),
      P ∈ S ∧ Q ∈ S ∧ P.submodule ≤ W i ∧ Q.submodule ≤ W i ∧ P ≠ Q := by
    have hc : 1 < (S.filter (fun P => P.submodule ≤ W i)).card := by
      have := hM i
      omega
    obtain ⟨P,hP,Q,hQ,hPQ⟩ := Finset.one_lt_card.mp hc
    exact ⟨P,Q,(mem_filter.mp hP).1,(mem_filter.mp hQ).1,
      (mem_filter.mp hP).2,(mem_filter.mp hQ).2,hPQ⟩
  choose P Q hPS hQS hP hQ hPQ using htwo
  let x (i : ι) := coord a (P i)
  let v (i : ι) := coord a (Q i)-coord a (P i)
  let T := S.image (coord (K := K) a)
  have hTc : T.card = S.card := card_image_of_injOn (fun P hP Q hQ hh =>
    coord_injOn a (ha P hP) (ha Q hQ) hh)
  have hA (i : ι) : AffineIncidence.onLine x v T i =
      (S.filter (fun P => P.submodule ≤ W i)).image (coord (K := K) a) := by
    ext z
    simp only [AffineIncidence.onLine,T,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨R,hRS,rfl⟩,t,ht⟩
      refine ⟨R,⟨hRS,?_⟩,rfl⟩
      apply (coord_mem_line a (W i) (hW i) (P i) (Q i) R
        (hPQ i) (hP i) (hQ i) (ha _ (hPS i)) (ha _ (hQS i)) (ha R hRS)).mpr
      exact ⟨t,ht.symm⟩
    · rintro ⟨R,⟨hRS,hRW⟩,rfl⟩
      refine ⟨⟨R,hRS,rfl⟩,?_⟩
      obtain ⟨t,ht⟩ := (coord_mem_line a (W i) (hW i) (P i) (Q i) R
        (hPQ i) (hP i) (hQ i) (ha _ (hPS i)) (ha _ (hQS i)) (ha R hRS)).mp hRW
      exact ⟨t,ht.symm⟩
  have hAc (i : ι) : (AffineIncidence.onLine x v T i).card =
      (S.filter (fun P => P.submodule ≤ W i)).card := by
    rw [hA]
    apply card_image_of_injOn
    intro P hP Q hQ hh
    exact coord_injOn a (ha P (mem_filter.mp hP).1) (ha Q (mem_filter.mp hQ).1) hh
  have H := RichAffineLines.card_mul_le h2 T (hS.image _) x v
    (fun i => line_coord_ne a (P i) (Q i) (ha _ (hPS i)) (ha _ (hQS i)) (hPQ i))
    (carriers_injective a W hW hd P Q hPQ hP hQ (fun i => ha _ (hPS i)) (fun i => ha _ (hQS i)))
    M Kp h C p hp hp1 (fun i => by rw [hAc]; exact hM i)
    (plane_cap_transfer S a ha Kp hcap) hprob
    (by rw [hTc]; exact hsize) hdeg hchar hMD hKM (by rw [hTc]; exact hD)
  simpa only [hTc] using H

end
end SharpLogRamsey.RichProjectiveLines
end

section

namespace SharpLogRamsey.RichLineScales
open scoped BigOperators
noncomputable section

theorem choose_parameters (N M q : ℕ) (hM : 0 < M) (hMN : M ≤ N)
    (hsmall : 198*Real.sqrt ((N:ℝ)/M) < M)
    (hchar : 33*Real.sqrt ((N:ℝ)/M) < q)
    (hprob : (N:ℝ)^2*Real.exp (-5*Real.sqrt ((N:ℝ)/M)) < 1/2) :
    ∃ h : ℕ, ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      (N:ℝ)^2*Real.exp (-p*M/12) < 1/2 ∧
      2*p*N < ((h+1)^3:ℕ) ∧ (3*h:ℕ) ≤ p*M/2 ∧
      3*h < q ∧ 18*h < M ∧ h^2*M ≤ 121*N := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hmn : (M:ℝ) ≤ N := by exact_mod_cast hMN
  let r := Real.sqrt ((N:ℝ)/M)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : 1 ≤ r := by
    have := Real.sqrt_le_sqrt ((le_div_iff₀ hm).mpr (by linarith : 1*(M:ℝ) ≤ N))
    simpa only [Real.sqrt_one] using this
  have hr : r^2*(M:ℝ) = N := by
    rw [Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hm.ne']
  let h : ℕ := ⌈10*r⌉₊
  have hhlo : 10*r ≤ (h:ℝ) := Nat.le_ceil _
  have hhhi : (h:ℝ) ≤ 11*r := by
    have H := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 10*r)
    change (h:ℝ) < 10*r+1 at H
    linarith
  have hhpos : (0:ℝ) < h := by linarith
  have hhm : 18*(h:ℝ) < M := by
    change 198*r < M at hsmall
    linarith
  have hhq : 3*(h:ℝ) < q := by
    change 33*r < q at hchar
    linarith
  let p : ℝ := 6*h/M
  have hp : 0 < p := div_pos (by positivity) hm
  have hpm : p*M = 6*h := by dsimp [p]; rw [div_mul_cancel₀ _ hm.ne']
  have hp1 : p ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  have hhsq : (h:ℝ)^2 ≤ 121*r^2 := by
    have := mul_le_mul hhhi hhhi (by positivity) (by positivity)
    nlinarith
  have hdsq : (h:ℝ)^2*(M:ℝ) ≤ 121*N := by
    have := mul_le_mul_of_nonneg_right hhsq hm.le
    nlinarith [hr]
  have hhbig : 12*r^2 < (h:ℝ)^2 := by
    have := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 10*r) hhlo
    nlinarith [sq_nonneg (r-1)]
  refine ⟨h,p,hp,hp1,?_,?_,?_,?_,?_,?_⟩
  · apply lt_of_le_of_lt _ hprob
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    rw [neg_mul, hpm]
    change -(6*(h:ℝ))/12 ≤ -5*r
    linarith
  · have hhN : 12*(N:ℝ) < (h:ℝ)^2*M := by
      have := mul_lt_mul_of_pos_right hhbig hm
      nlinarith [hr]
    have hsize' : 2*p*N < (h:ℝ)^3 := by
      have h1 : 2*p*N*M < (h:ℝ)^3*M := by
        calc
          _ = 12*(h:ℝ)*N := by nlinarith [congrArg (fun x : ℝ => 2*(N:ℝ)*x) hpm]
          _ < (h:ℝ)*((h:ℝ)^2*M) := by nlinarith [mul_lt_mul_of_pos_left hhN hhpos]
          _ = _ := by ring
      exact (mul_lt_mul_iff_left₀ hm).mp (by simpa only [mul_comm _ (M:ℝ)] using h1)
    have hnext : (h:ℝ)^3 < ((h:ℝ)+1)^3 := by nlinarith [sq_nonneg (h:ℝ)]
    exact_mod_cast hsize'.trans hnext
  · simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hpm]
    linarith
  · exact_mod_cast hhq
  · exact_mod_cast hhm
  · exact_mod_cast hdsq

end
end SharpLogRamsey.RichLineScales
end

section

namespace SharpLogRamsey.RichProjectiveCount
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]
    [Infinite E] [IsAlgClosed E] [Fintype ι]

theorem card_mul_le {q : ℕ} [CharP E q] (h2 : (2:E) ≠ 0)
    (S : Finset (Projectivization K (Fin 4 → K))) (hS : S.Nonempty)
    (W : ι → Submodule K (Fin 4 → K))
    (hW : ∀ i, Module.finrank K (W i) = 2) (hd : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ S.card)
    (hM : ∀ i, M ≤ (S.filter (fun P => P.submodule ≤ W i)).card)
    (hcap : ∀ f : (Fin 4 → K) →ₗ[K] K, f ≠ 0 →
      (S.filter (fun P => f P.rep = 0)).card ≤ Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M) < M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M) < q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M)) < 1/2)
    (hKM : 8*Kp ≤ M^2) : Fintype.card ι*M ≤ 8718*S.card := by
  obtain ⟨h,p,hp,hp1,hprob',hsize,hdeg,hchar',hMD,hD⟩ :=
    RichLineScales.choose_parameters S.card M q (by omega) hMN hsmall hchar hprob
  have hc := RichProjectiveLines.card_lines_square S W hW hd (fun i => hM2.trans (hM i))
  have hprob'' : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2 := by
    apply lt_of_le_of_lt _ hprob'
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact_mod_cast hc
  exact RichProjectiveLines.card_mul_le (E := E) h2 S hS W hW hd M Kp h 121 hM2
    p hp hp1 hM hcap hprob'' hsize hdeg hchar' hMD hKM hD

end
end SharpLogRamsey.RichProjectiveCount
end

section

namespace SharpLogRamsey.RichFiniteProjective
open scoped BigOperators
open Finset Classical
noncomputable section
variable {q : ℕ} [Fact q.Prime] {ι : Type*} [Fintype ι]

theorem card_mul_le (hq : 3 ≤ q)
    (S : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))) (hS : S.Nonempty)
    (W : ι → Submodule (ZMod q) (Fin 4 → ZMod q))
    (hW : ∀ i, Module.finrank (ZMod q) (W i) = 2) (hd : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ S.card)
    (hM : ∀ i, M ≤ (S.filter (fun P => P.submodule ≤ W i)).card)
    (hcap : ∀ f : (Fin 4 → ZMod q) →ₗ[ZMod q] ZMod q, f ≠ 0 →
      (S.filter (fun P => f P.rep = 0)).card ≤ Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M) < M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M) < q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M)) < 1/2)
    (hKM : 8*Kp ≤ M^2) : Fintype.card ι*M ≤ 8718*S.card := by
  apply RichProjectiveCount.card_mul_le (E := AlgebraicClosure (ZMod q))
    (q := q) _ S hS W hW hd M Kp hM2 hMN hM (by
      intro functional nonzero
      convert! (preTransparency := .all) hcap functional nonzero) hsmall hchar hprob hKM
  intro hh
  have hdiv : q ∣ 2 := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q 2).mp
    (by simpa only [Nat.cast_ofNat] using hh)
  have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

end
end SharpLogRamsey.RichFiniteProjective
end

end

end OAI
