import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Triple

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.NonplaneRichLines
open Finset MvPolynomial
open AffineIncidence
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
variable {ι : Type*} [Fintype ι]
theorem card_le {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (S : Finset (Fin 3 → K)) (M : ℕ) (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hMD : 3*F.totalDegree < M) :
    Fintype.card ι ≤ 2*S.card/(M-3*F.totalDegree)+6*F.totalDegree^2 := by
  classical
  obtain ⟨Q,hQ,hQD,hQr⟩ := RichLinePolynomial.auxiliary_polynomial F hF hdeg hs h2 hn
  let bad := univ.filter (fun i => (richPoints x v S i).card ≤ 3*F.totalDegree)
  let good := univ.filter (fun i => 3*F.totalDegree < (richPoints x v S i).card)
  have hb : bad.card ≤ 2*S.card/(M-3*F.totalDegree) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    exact pruning_bound x v S M (3*F.totalDegree) hM
  have hgood : ∀ i ∈ good, LineFlatness.restrictLine (x i) (v i) Q = 0 := by
    intro i hi
    obtain ⟨T,hcard,hT⟩ := many_parameters x v hv S i
    apply hQr (x i) (v i) T (by rw [hcard]; exact (mem_filter.mp hi).2)
    intro t ht
    exact three_lines_at_rich F x v hv hd hzero _ (hT t ht)
  have hg : good.card ≤ 6*F.totalDegree^2 := by
    have H := CommonLines.card_le F Q hQ (fun i : good => x i) (fun i : good => v i)
      (fun i => hv i) (fun i j H => Subtype.ext (hd H))
      (fun i t => eval_of_restrict_zero _ _ F (hzero i) _ ⟨t,rfl⟩)
      (fun i t => eval_of_restrict_zero _ _ Q (hgood i i.property) _ ⟨t,rfl⟩)
    have H' : good.card ≤ 2*F.totalDegree*Q.totalDegree := by simpa using H
    calc
      _ ≤ 2*F.totalDegree*Q.totalDegree := H'
      _ ≤ 2*F.totalDegree*(3*F.totalDegree) := Nat.mul_le_mul_left _ hQD
      _ = 6*F.totalDegree^2 := by ring
  have hsplit : bad.card+good.card = Fintype.card ι := by
    simpa only [bad,good,not_le,card_univ] using
      card_filter_add_card_filter_not (s := univ) (p := fun i => (richPoints x v S i).card ≤ 3*F.totalDegree)
  omega

end
end SharpLogRamsey.NonplaneRichLines

section

namespace SharpLogRamsey.PlaneDecomposition
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

lemma unit_of_degree_zero (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (h : F.totalDegree = 0) : IsUnit F := by
  have he := totalDegree_eq_zero_iff_eq_C.mp h
  have hc : F.coeff 0 ≠ 0 := by
    intro H
    apply hF
    rw [he,H,map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem exists_decomposition (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (hs : Squarefree F) :
    ∃ (planes : List (MvPolynomial (Fin 3) K)) (G : MvPolynomial (Fin 3) K),
      G ≠ 0 ∧ Squarefree G ∧ F = planes.prod*G ∧
      (∀ L ∈ planes, L.totalDegree = 1) ∧
      planes.Pairwise IsRelPrime ∧
      (∀ L ∈ planes, L ∣ F) ∧
      (∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) ∧
      planes.length+G.totalDegree = F.totalDegree := by
  classical
  suffices H : ∀ n (F : MvPolynomial (Fin 3) K), F.totalDegree = n → F ≠ 0 → Squarefree F →
    ∃ (planes : List (MvPolynomial (Fin 3) K)) (G : MvPolynomial (Fin 3) K),
      G ≠ 0 ∧ Squarefree G ∧ F = planes.prod*G ∧
      (∀ L ∈ planes, L.totalDegree = 1) ∧ planes.Pairwise IsRelPrime ∧
      (∀ L ∈ planes, L ∣ F) ∧
      (∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) ∧
      planes.length+G.totalDegree = F.totalDegree by
    exact H F.totalDegree F rfl hF hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn hF hs
    by_cases hno : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L
    · exact ⟨[],F,hF,hs,by simp,by simp,by simp,by simp,hno,by simp⟩
    push Not at hno
    obtain ⟨L,hLF,hd,hnu⟩ := hno
    have hL : L ≠ 0 := ne_zero_of_dvd_ne_zero hF hLF
    have hdL : L.totalDegree = 1 := by
      have hn0 : L.totalDegree ≠ 0 := fun h => hnu (unit_of_degree_zero L hL h)
      omega
    obtain ⟨A,hFA⟩ := hLF
    have hA : A ≠ 0 := by
      intro H
      apply hF
      rw [hFA,H,mul_zero]
    have hde : F.totalDegree = 1+A.totalDegree := by
      rw [hFA,totalDegree_mul_of_isDomain hL hA,hdL]
    have hAl : A.totalDegree < n := by omega
    have hsq := squarefree_mul_iff.mp (hFA ▸ hs)
    obtain ⟨planes,G,hG,hGs,hAG,hplanes,hpair,hdiv,hng,hdeg⟩ :=
      ih A.totalDegree hAl A rfl hA hsq.2.2
    refine ⟨L::planes,G,hG,hGs,?_,?_,?_,?_,hng,?_⟩
    · simp only [List.prod_cons]
      rw [mul_assoc,← hAG,← hFA]
    · intro J hJ
      obtain rfl | hJ := List.mem_cons.mp hJ
      · exact hdL
      · exact hplanes J hJ
    · apply List.pairwise_cons.mpr
      exact ⟨fun J hJ => hsq.1.of_dvd_right (hdiv J hJ),hpair⟩
    · intro J hJ
      obtain rfl | hJ := List.mem_cons.mp hJ
      · exact ⟨A,hFA⟩
      · exact (hdiv J hJ).trans (hFA ▸ dvd_mul_left A L)
    · simp only [List.length_cons]
      omega

end
end SharpLogRamsey.PlaneDecomposition

end

section

namespace SharpLogRamsey.PlaneCount
open Finset
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq X]
noncomputable section
omit [DecidableEq ι] in

lemma incidence_sum (A : ι → Finset X) (U : Finset X) (hU : ∀ i, A i ⊆ U) :
    (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card) = ∑ i, (A i).card := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have H : U.filter (fun x => x ∈ A i) = A i := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hU i h,h⟩⟩
  rw [← card_filter,H]
omit [DecidableEq ι] in

lemma incidence_sq_sum (A : ι → Finset X) (U : Finset X) (hU : ∀ i, A i ⊆ U) :
    (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card^2) =
      ∑ i, ∑ j, (A i ∩ A j).card := by
  classical
  have he (x : X) : (univ.filter (fun i => x ∈ A i)).card^2 =
      ∑ i, ∑ j, if x ∈ A i ∧ x ∈ A j then (1:ℕ) else 0 := by
    simp only [card_filter,pow_two,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    by_cases H : x ∈ A i <;> by_cases H' : x ∈ A j <;> simp [H,H']
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have H : U.filter (fun x => x ∈ A i ∧ x ∈ A j) = A i ∩ A j := by
    ext x
    simp only [mem_filter,mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hU i h.1,h⟩⟩
  rw [← card_filter,H]

theorem card_mul_le (A : ι → Finset X) (U : Finset X) (M K : ℕ)
    (hU : ∀ i, A i ⊆ U) (hM : ∀ i, (A i).card = M)
    (hi : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hK : U.card ≤ K) (hMK : 2*K ≤ M^2) (hM0 : 0 < M) :
    Fintype.card ι*M ≤ 2*K := by
  classical
  let u := Fintype.card ι
  have hs : (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card) = u*M := by
    rw [incidence_sum A U hU]
    simp [hM,u]
  have hs2 : (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card^2) ≤ u*(M+u) := by
    rw [incidence_sq_sum A U hU]
    calc
      _ ≤ ∑ i : ι, ∑ j : ι, ((if i = j then M else 0)+1) := by
        apply sum_le_sum; intro i _
        apply sum_le_sum; intro j _
        by_cases H : i = j
        · subst j; simp [hM]
        · simpa [H] using (hi i j H)
      _ = u*(M+u) := by simp [u,sum_add_distrib]
  have hcs := sq_sum_le_card_mul_sum_sq (s := U)
    (f := fun x => (univ.filter (fun i => x ∈ A i)).card)
  rw [hs] at hcs
  have H : (u*M)^2 ≤ K*(u*(M+u)) := hcs.trans (Nat.mul_le_mul hK hs2)
  by_cases hu : u = 0
  · change u*M ≤ 2*K
    simp [hu]
  have hu0 : 0 < u := Nat.pos_of_ne_zero hu
  have hcancel : u*M^2 ≤ K*(M+u) := by
    apply Nat.le_of_mul_le_mul_left (c := u)
    calc
      u*(u*M^2) = (u*M)^2 := by ring
      _ ≤ K*(u*(M+u)) := H
      _ = u*(K*(M+u)) := by ring
    exact hu0
  have hmid : u*M^2 ≤ 2*K*M := by nlinarith [Nat.mul_le_mul_left u hMK]
  change u*M ≤ 2*K
  apply Nat.le_of_mul_le_mul_right (c := M)
  · nlinarith
  · exact hM0

lemma exclusive_card (A : ι → Finset X) (i : ι)
    (hi : ∀ j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    (A i).card ≤ (A i \ (univ.erase i).biUnion A).card+Fintype.card ι := by
  classical
  have he : A i ∩ (univ.erase i).biUnion A =
      (univ.erase i).biUnion (fun j => A i ∩ A j) := by
    ext x
    simp only [mem_inter,mem_biUnion]
    aesop
  have h : (A i ∩ (univ.erase i).biUnion A).card ≤ Fintype.card ι := by
    rw [he]
    calc
      _ ≤ ∑ j ∈ univ.erase i, (A i ∩ A j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase i, 1 := by
        apply sum_le_sum
        intro j hj
        exact hi j (mem_erase.mp hj).1.symm
      _ ≤ Fintype.card ι := by simp
  have hs := card_sdiff_add_card_inter (A i) ((univ.erase i).biUnion A)
  omega

lemma exclusive_disjoint (A : ι → Finset X) :
    (↑(univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => A i \ (univ.erase i).biUnion A) := by
  classical
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro x hxi hxj
  have hxi' := mem_sdiff.mp hxi
  have hxj' := mem_sdiff.mp hxj
  apply hxi'.2
  apply mem_biUnion.mpr
  exact ⟨j,mem_erase.mpr ⟨hij.symm,mem_univ j⟩,hxj'.1⟩

theorem union_lower (A : ι → Finset X) (M : ℕ)
    (hM : ∀ i, M ≤ (A i).card)
    (hi : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    Fintype.card ι*(M-Fintype.card ι) ≤ (univ.biUnion A).card := by
  classical
  let E := fun i => A i \ (univ.erase i).biUnion A
  calc
    _ = ∑ _i : ι, (M-Fintype.card ι) := by simp
    _ ≤ ∑ i, (E i).card := by
      apply sum_le_sum
      intro i _
      have H := exclusive_card A i (hi i)
      have hm := hM i
      dsimp [E]
      omega
    _ = (univ.biUnion E).card := (card_biUnion (exclusive_disjoint A)).symm
    _ ≤ (univ.biUnion A).card := by
      apply card_le_card
      intro x hx
      obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨i,hi,(mem_sdiff.mp hx).1⟩

end
end SharpLogRamsey.PlaneCount

namespace SharpLogRamsey.SinglePlaneCount
open Finset
open scoped BigOperators
variable {κ ι X : Type*} [Fintype κ] [Fintype ι] [DecidableEq X]
noncomputable section

theorem card_mul_le (A : ι → Finset X) (P : κ → Finset X) (owner : ι → κ)
    (U : Finset X) (M K : ℕ) (hM0 : 0 < M)
    (hM : ∀ i, (A i).card = M)
    (hAU : ∀ i, A i ⊆ P (owner i)) (hPU : ∀ j, P j ⊆ U)
    (hcap : ∀ j, (P j).card ≤ K)
    (hcross : ∀ i j, j ≠ owner i → (A i ∩ P j).card ≤ 1)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hKM : 8*K ≤ M^2) (hDM : 4*Fintype.card κ ≤ M) :
    Fintype.card ι*M ≤ 2*U.card := by
  classical
  let D := Fintype.card κ
  let Region (j : κ) := P j \ (univ.erase j).biUnion P
  let u (j : κ) := Fintype.card {i : ι // owner i = j}
  have hu (j : κ) : 4*u j ≤ M := by
    have H := PlaneCount.card_mul_le (fun i : {i : ι // owner i = j} => A i.val)
      (P j) M K (by intro i; simpa [i.property] using hAU i.val)
      (fun i => hM i.val) (fun i k hik => hpair i.val k.val (by intro he; exact hik (Subtype.ext he)))
      (hcap j) (by omega) hM0
    change u j*M ≤ 2*K at H
    apply Nat.le_of_mul_le_mul_right (c := M)
    · nlinarith
    · exact hM0
  have hlocal (j : κ) : u j*M ≤ 2*(Region j).card := by
    let E : {i : ι // owner i = j} → Finset X := fun i => A i.val \ (univ.erase j).biUnion P
    have hEc (i : {i : ι // owner i = j}) : M-D ≤ (E i).card := by
      have he : A i.val ∩ (univ.erase j).biUnion P =
          (univ.erase j).biUnion (fun k => A i.val ∩ P k) := by
        ext a
        simp only [mem_inter,mem_biUnion]
        aesop
      have H : (A i.val ∩ (univ.erase j).biUnion P).card ≤ D := by
        rw [he]
        calc
          _ ≤ ∑ k ∈ univ.erase j, (A i.val ∩ P k).card := card_biUnion_le
          _ ≤ ∑ _k ∈ univ.erase j, 1 := by
            apply sum_le_sum
            intro k hk
            apply hcross
            simpa [i.property] using (mem_erase.mp hk).1
          _ ≤ D := by simp [D]
      have H' := card_sdiff_add_card_inter (A i.val) ((univ.erase j).biUnion P)
      rw [hM] at H'
      change M-D ≤ (A i.val \ (univ.erase j).biUnion P).card
      omega
    have hE (i : {i : ι // owner i = j}) : E i ⊆ Region j := by
      intro a ha
      obtain ⟨ha,hn⟩ := mem_sdiff.mp ha
      apply mem_sdiff.mpr
      exact ⟨by simpa [i.property] using hAU i.val ha,hn⟩
    have hp (i k : {i : ι // owner i = j}) (hik : i ≠ k) : (E i ∩ E k).card ≤ 1 := by
      apply le_trans (card_le_card ?_) (hpair i.val k.val (by intro he; exact hik (Subtype.ext he)))
      intro a ha
      exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp ha).1).1,(mem_sdiff.mp (mem_inter.mp ha).2).1⟩
    have H := PlaneCount.union_lower E (M-D) hEc hp
    have H' : (univ.biUnion E).card ≤ (Region j).card := by
      apply card_le_card
      intro a ha
      obtain ⟨i,hi,ha⟩ := mem_biUnion.mp ha
      exact hE i ha
    have hnum : M ≤ 2*(M-D-u j) := by
      have h1 := hu j
      change 4*D ≤ M at hDM
      omega
    change u j*(M-D-u j) ≤ (univ.biUnion E).card at H
    nlinarith [Nat.mul_le_mul_left (u j) hnum]
  have hregions : (↑(univ : Finset κ) : Set κ).PairwiseDisjoint Region :=
    PlaneCount.exclusive_disjoint P
  have hregionU : univ.biUnion Region ⊆ U := by
    intro a ha
    obtain ⟨j,hj,ha⟩ := mem_biUnion.mp ha
    exact hPU j (mem_sdiff.mp ha).1
  have hsumu : ∑ j, u j = Fintype.card ι := by
    simp only [u,Fintype.card_subtype]
    exact (card_eq_sum_card_fiberwise (s := (univ : Finset ι)) (t := univ)
      (by intro _ _; exact mem_univ _)).symm
  calc
    _ = ∑ j, u j*M := by rw [← sum_mul,hsumu]
    _ ≤ ∑ j, 2*(Region j).card := sum_le_sum (fun j _ => hlocal j)
    _ = 2*(univ.biUnion Region).card := by rw [card_biUnion hregions,mul_sum]
    _ ≤ 2*U.card := Nat.mul_le_mul_left _ (card_le_card hregionU)

end
end SharpLogRamsey.SinglePlaneCount

end

namespace SharpLogRamsey.SurfaceRichLines
open MvPolynomial Finset AffineIncidence
open scoped BigOperators Classical
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
omit [Infinite K] in

lemma plane_crossing (S : Finset (Fin 3 → K)) (x v : Fin 3 → K) (hv : v ≠ 0)
    (L : MvPolynomial (Fin 3) K) (hL : L.totalDegree ≤ 1)
    (hn : LineFlatness.restrictLine x v L ≠ 0) :
    (S.filter (fun y => y ∈ carrier x v ∧ eval y L = 0)).card ≤ 1 := by
  classical
  let A := S.filter (fun y => y ∈ carrier x v ∧ eval y L = 0)
  let f : K → Fin 3 → K := fun t => x+t • v
  let T := A.preimage f (parametrization_injective _ _ hv).injOn
  have hc : T.card = A.card := by
    rw [card_preimage]
    congr 1
    apply filter_eq_self.mpr
    intro y hy
    exact (mem_filter.mp hy).2.1
  have H : T.card ≤ (LineFlatness.restrictLine x v L).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    apply (Polynomial.mem_roots hn).mpr
    change Polynomial.eval t (LineFlatness.restrictLine x v L) = 0
    rw [RichLinePolynomial.restriction_eval]
    have H := (mem_filter.mp (mem_preimage.mp ht)).2.2
    have he : f t = (fun j => x j+v j*t) := by ext j; simp [f,mul_comm]
    simpa only [he] using H
  rw [hc] at H
  exact H.trans ((RichLinePolynomial.restriction_degree x v L).trans hL)

variable {ι : Type*} [Fintype ι]

theorem card_le {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (S : Finset (Fin 3 → K)) (M Kp : ℕ)
    (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hcap : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree = 1 →
      (S.filter (fun y => eval y L = 0)).card ≤ Kp)
    (hMD : 6*F.totalDegree < M) (hKM : 8*Kp ≤ M^2) :
    Fintype.card ι ≤ 2*S.card/M+2*S.card/(M-3*F.totalDegree)+8*F.totalDegree^2 := by
  classical
  obtain ⟨planes,G,hG,hGs,hprod,hplanes,hpair,hdiv,hng,hde⟩ :=
    PlaneDecomposition.exists_decomposition F hF hs
  let κ := Fin planes.length
  let L : κ → MvPolynomial (Fin 3) K := planes.get
  have hLd (j : κ) : (L j).totalDegree = 1 := hplanes _ (List.get_mem planes j)
  have hLdiv (j : κ) : L j ∣ F := hdiv _ (List.get_mem planes j)
  have hLc (j k : κ) (hjk : j ≠ k) : IsRelPrime (L j) (L k) := by
    rcases lt_or_gt_of_ne hjk with H | H
    · exact hpair.rel_get_of_lt H
    · exact (hpair.rel_get_of_lt H).symm
  let On : ι → κ → Prop := fun i j => LineFlatness.restrictLine (x i) (v i) (L j) = 0
  let multiple : Finset ι := univ.filter (fun i => ∃ j k, j ≠ k ∧ On i j ∧ On i k)
  let single : Finset ι := univ.filter (fun i => (∃ j, On i j) ∧ i ∉ multiple)
  let none : Finset ι := univ.filter (fun i => ¬∃ j, On i j)
  have hm : multiple.card ≤ 2*F.totalDegree^2 := by
    let Both (j k : κ) := univ.filter (fun i => On i j ∧ On i k)
    have hB (j k : κ) (hjk : j ≠ k) : (Both j k).card ≤ 2 := by
      have H := CommonLines.card_le (L j) (L k) (hLc j k hjk)
        (fun i : Both j k => x i) (fun i : Both j k => v i) (fun i => hv i)
        (fun i l H => Subtype.ext (hd H))
        (fun i t => NonplaneRichLines.eval_of_restrict_zero _ _ _ (mem_filter.mp i.property).2.1 _ ⟨t,rfl⟩)
        (fun i t => NonplaneRichLines.eval_of_restrict_zero _ _ _ (mem_filter.mp i.property).2.2 _ ⟨t,rfl⟩)
      simpa only [Fintype.card_coe,hLd,mul_one] using H
    have hc : multiple ⊆ univ.biUnion (fun j : κ => (univ.erase j).biUnion (Both j)) := by
      intro i hi
      obtain ⟨j,k,hjk,hj,hk⟩ := (mem_filter.mp hi).2
      exact mem_biUnion.mpr ⟨j,mem_univ j,mem_biUnion.mpr
        ⟨k,mem_erase.mpr ⟨hjk.symm,mem_univ k⟩,mem_filter.mpr ⟨mem_univ i,hj,hk⟩⟩⟩
    calc
      _ ≤ (univ.biUnion (fun j : κ => (univ.erase j).biUnion (Both j))).card := card_le_card hc
      _ ≤ ∑ j : κ, ((univ.erase j).biUnion (Both j)).card := card_biUnion_le
      _ ≤ ∑ j : κ, ∑ k ∈ univ.erase j, 2 := by
        apply sum_le_sum
        intro j hj
        apply le_trans card_biUnion_le
        apply sum_le_sum
        intro k hk
        exact hB j k (mem_erase.mp hk).1.symm
      _ ≤ 2*planes.length^2 := by
        simp only [sum_const, Nat.nsmul_eq_mul, card_erase_of_mem (mem_univ _), card_univ]
        have H : planes.length - 1 ≤ planes.length := Nat.sub_le _ _
        dsimp [κ]
        simp only [Fintype.card_fin]
        nlinarith [Nat.mul_le_mul_left planes.length H]
      _ ≤ 2*F.totalDegree^2 := by nlinarith
  have hsing : single.card ≤ 2*S.card/M := by
    have howner : ∀ i : single, ∃ j, On i.val j := fun i => (mem_filter.mp i.property).2.1
    choose owner ho using howner
    have hchoices : ∀ i : single, ∃ A ⊆ onLine x v S i.val, A.card = M :=
      fun i => exists_subset_card_eq (hM i.val)
    choose A hA hAc using hchoices
    let P : κ → Finset (Fin 3 → K) := fun j => S.filter (fun y => eval y (L j) = 0)
    have hAP (i : single) : A i ⊆ P (owner i) := by
      intro y hy
      have hy' := mem_filter.mp (hA i hy)
      apply mem_filter.mpr
      exact ⟨hy'.1,NonplaneRichLines.eval_of_restrict_zero _ _ _ (ho i) y hy'.2⟩
    have hc (i : single) (j : κ) (hj : j ≠ owner i) : (A i ∩ P j).card ≤ 1 := by
      have hn : ¬On i.val j := by
        intro H
        exact (mem_filter.mp i.property).2.2 (mem_filter.mpr ⟨mem_univ i.val,
          j,owner i,hj,H,ho i⟩)
      apply le_trans (card_le_card ?_) (plane_crossing S (x i) (v i) (hv i) (L j) (hLd j).le hn)
      intro y hy
      have hAi := mem_filter.mp (hA i (mem_inter.mp hy).1)
      exact mem_filter.mpr ⟨hAi.1,hAi.2,(mem_filter.mp (mem_inter.mp hy).2).2⟩
    have hp (i k : single) (hik : i ≠ k) : (A i ∩ A k).card ≤ 1 := by
      exact points_intersection_le (fun i : single => x i) (fun i : single => v i)
        (fun i => hv i) (fun i k H => Subtype.ext (hd H)) A
        (fun i _ hy => (mem_filter.mp (hA i hy)).2) i k hik
    have H := SinglePlaneCount.card_mul_le A P owner S M Kp (by omega) hAc hAP
      (fun j => filter_subset _ _) (fun j => hcap (L j) (hLdiv j) (hLd j)) hc hp hKM
      (by simp only [κ,Fintype.card_fin]; omega)
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    simpa only [Fintype.card_coe] using H
  have hn : none.card ≤ 2*S.card/(M-3*F.totalDegree)+6*F.totalDegree^2 := by
    have hz (i : none) : LineFlatness.restrictLine (x i) (v i) G = 0 := by
      let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
        aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)
      have H : φ F = 0 := hzero i
      rw [hprod,map_mul] at H
      apply (mul_eq_zero.mp H).resolve_left
      intro hp0
      rw [map_list_prod,List.prod_eq_zero_iff,List.mem_map] at hp0
      obtain ⟨J,hJ,hφJ⟩ := hp0
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hJ
      exact (mem_filter.mp i.property).2 ⟨j,hφJ⟩
    have H := NonplaneRichLines.card_le G hG (by omega) hGs h2 hng
      (fun i : none => x i) (fun i : none => v i) (fun i => hv i)
      (fun i k H => Subtype.ext (hd H)) hz S M (fun i => hM i) (by omega)
    have H' : none.card ≤ 2*S.card/(M-3*G.totalDegree)+6*G.totalDegree^2 := by
      simpa only [Fintype.card_coe] using H
    apply H'.trans
    apply Nat.add_le_add
    · exact Nat.div_le_div_left (by omega) (by omega)
    · nlinarith
  have hsplit : Fintype.card ι ≤ single.card+multiple.card+none.card := by
    have H : (univ : Finset ι) ⊆ single ∪ multiple ∪ none := by
      intro i hi
      by_cases he : ∃ j, On i j
      · by_cases hm : i ∈ multiple
        · exact mem_union_left _ (mem_union_right _ hm)
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,he,hm⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hi,he⟩)
    have H' := (card_le_card H).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    simpa only [card_univ] using H'
  omega

end
end SharpLogRamsey.SurfaceRichLines

section

section

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]

end SharpLogRamsey.Sampling
end
end
end
end

end OAI
