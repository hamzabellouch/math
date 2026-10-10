import OAI.Analysis.RotationWeights.FiniteSampling

namespace OAI

noncomputable section

namespace CircleSampling

universe uV

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology

section
open scoped Topology
lemma phase_success_eventually {m : ℕ} (γ : PhaseCube m) {k : ℤ} {i : Fin m} {b : ℝ}
    (hne : ((k*(γ i:ℝ):ℝ):CircleX) ≠ 0) (hgood : (γ i:ℝ) ∉ phaseFailure b k) :
    ∀ᶠ β : PhaseCube m in 𝓝 γ, (β i:ℝ) ∉ phaseFailure b k := by
  have heval : ContinuousAt (fun β : PhaseCube m => (β i:ℝ)) γ :=
    continuous_subtype_val.continuousAt.comp (continuous_apply i).continuousAt
  have hc : ContinuousAt (fun β : PhaseCube m => repr ((k*(β i:ℝ):ℝ):CircleX)) γ :=
    (continuousAt_repr hne).comp (f:=fun β : PhaseCube m => ((k*(β i:ℝ):ℝ):CircleX))
      ((AddCircle.continuous_mk' 1).continuousAt.comp (continuousAt_const.mul heval))
  have hh : b < 1-repr ((k*(γ i:ℝ):ℝ):CircleX) ∧ 1-repr ((k*(γ i:ℝ):ℝ):CircleX) < 1-b :=
    by simpa [phaseFailure] using hgood
  have hc' : ContinuousAt (fun β : PhaseCube m => 1-repr ((k*(β i:ℝ):ℝ):CircleX)) γ := continuousAt_const.sub hc
  filter_upwards [hc'.eventually (Ioo_mem_nhds hh.1 hh.2)] with β hβ
  simpa [phaseFailure] using hβ

lemma phase_cover_eventually {m : ℕ} (γ : PhaseCube m) (S : Finset ℤ) (b : ℝ)
    (hphase : ∀ k∈S, ∀ i, ((k*(γ i:ℝ):ℝ):CircleX) ≠ 0) :
    ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ k∈S,
      (Finset.univ.filter fun i => (γ i:ℝ) ∉ phaseFailure b k).card ≤
      (Finset.univ.filter fun i => (β i:ℝ) ∉ phaseFailure b k).card := by
  classical
  have hs : ∀ k∈S, ∀ᶠ β : PhaseCube m in 𝓝 γ,
      ∀ i, (γ i:ℝ) ∉ phaseFailure b k → (β i:ℝ) ∉ phaseFailure b k := by
    intro k hk
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : (γ i:ℝ) ∉ phaseFailure b k
    · exact (phase_success_eventually γ (hphase k hk i) hi).mono (fun β hb _ => hb)
    · exact Filter.Eventually.of_forall (fun _ hi' => (hi hi').elim)
  filter_upwards [(Filter.eventually_all_finite S.finite_toSet).mpr hs] with β hβ k hk
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hβ k hk i (Finset.mem_filter.mp hi).2⟩

lemma cube_interval_eventually {m : ℕ} (γ : PhaseCube m) {a b : ℝ}
    (hγ : ∀ i, (γ i:ℝ)∈Set.Ioo a b) :
    ∀ᶠ β : PhaseCube m in 𝓝 γ, ∀ i, (β i:ℝ)∈Set.Ioo a b := by
  apply Filter.eventually_all.mpr
  intro i
  exact (continuous_subtype_val.continuousAt.comp (continuous_apply i).continuousAt : ContinuousAt (fun β : PhaseCube m => (β i:ℝ)) γ).eventually
    (Ioo_mem_nhds (hγ i).1 (hγ i).2)
end

section
open scoped BigOperators

def phaseRange (N R : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊R⌋) ⌊R⌋).filter (fun k => N/4 ≤ |(k:ℝ)|)
lemma mem_phaseRange {N R : ℝ} {k : ℤ} (hk : N/4 ≤ |(k:ℝ)|) (hkR : |(k:ℝ)| ≤ R) :
    k∈phaseRange N R := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,hk⟩
  · have h : (-k:ℝ) ≤ R := by linarith [(abs_le.mp hkR).1]
    have hh : -k ≤ ⌊R⌋ := Int.le_floor.mpr (by simpa using h)
    omega
  · exact Int.le_floor.mpr (abs_le.mp hkR).2
lemma phaseRange_bound {N R : ℝ} (hR : 1 ≤ R) : (phaseRange N R).card ≤ 3*R := by
  have hR0 : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr (by linarith)
  calc
    ((phaseRange N R).card:ℝ) ≤ ((Finset.Icc (-⌊R⌋) ⌊R⌋).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    _ = 2*(⌊R⌋:ℝ)+1 := by
      rw [Int.card_Icc]
      have hh : 0 ≤ ⌊R⌋+1-(-⌊R⌋) := by omega
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hh]
      push_cast
      ring
    _ ≤ 3*R := by have := Int.floor_le R; linarith
lemma phaseRange_lower {N R : ℝ} {k : ℤ} (hk : k∈phaseRange N R) : N/4 ≤ |(k:ℝ)| :=
  (Finset.mem_filter.mp hk).2
end

open Set Topology
section

lemma rotation_syndetic {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ L : ℕ, 0 < L ∧ ∀ a : ℤ, ∃ n : ℤ,
      a ≤ n ∧ n < a+L ∧ n • (θ:CircleX) ∈ O := by
  classical
  have hd : DenseRange (fun n : ℤ => n • (θ:CircleX)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hθ)
  let U : ℤ → Set CircleX := fun n => (fun x => x+n•(θ:CircleX)) ⁻¹' O
  have hU : ∀ n, IsOpen (U n) := fun n => hO.preimage (by fun_prop)
  have hc : (univ : Set CircleX) ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨y,hy⟩ := hne
    have ho : IsOpen ((fun z : CircleX => x+z) ⁻¹' O) := hO.preimage (by fun_prop)
    obtain ⟨n,hn⟩ := hd.exists_mem_open ho ⟨y-x,by simpa using hy⟩
    exact mem_iUnion.mpr ⟨n,hn⟩
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover U hU hc
  let B : ℕ := S.sup Int.natAbs
  refine ⟨2*B+1,by omega,?_⟩
  intro a
  obtain ⟨k,hk,hx⟩ := mem_iUnion₂.mp (hS (mem_univ ((a+B)•(θ:CircleX))))
  have hb : k.natAbs ≤ B := Finset.le_sup (f := Int.natAbs) hk
  have hkle : k ≤ (B:ℤ) := (Int.le_natAbs (a:=k)).trans (by exact_mod_cast hb)
  have hkge : -(B:ℤ) ≤ k := by
    have hab : |k| ≤ (B:ℤ) := by
      simpa only [Int.natCast_natAbs] using (show (k.natAbs:ℤ) ≤ B by exact_mod_cast hb)
    exact (abs_le.mp hab).1
  refine ⟨a+B+k,by omega,by push_cast; omega,?_⟩
  simpa only [U,mem_preimage,add_zsmul] using hx

lemma return_samples {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ L : ℕ, 0 < L ∧ ∀ (a : ℤ) (P : ℕ), ∃ S : Finset ℤ,
      S.card=P ∧ ∀ n ∈ S, a ≤ n ∧ n < a+P*L ∧ n•(θ:CircleX) ∈ O := by
  classical
  obtain ⟨L,hL,hret⟩ := rotation_syndetic hθ hO hne
  refine ⟨L,hL,?_⟩
  intro a P
  choose n hn using (fun j : Fin P => hret (a+(j:ℤ)*L))
  have hinj : Function.Injective n := by
    intro j k he
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · have hcast : (j:ℤ)+1 ≤ (k:ℤ) := by exact_mod_cast hjk
      have hmul := mul_le_mul_of_nonneg_right hcast (show (0:ℤ) ≤ L by positivity)
      have hj := (hn j).2.1
      have hk := (hn k).1
      rw [he] at hj
      nlinarith
    · have hcast : (k:ℤ)+1 ≤ (j:ℤ) := by exact_mod_cast hkj
      have hmul := mul_le_mul_of_nonneg_right hcast (show (0:ℤ) ≤ L by positivity)
      have hj := (hn j).1
      have hk := (hn k).2.1
      rw [he] at hj
      nlinarith
  refine ⟨Finset.univ.image n,by simp [Finset.card_image_of_injective _ hinj],?_⟩
  intro k hk
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
  refine ⟨?_,?_,(hn j).2.2⟩
  · have hz : (0:ℤ) ≤ (j:ℤ)*L := by positivity
    exact le_trans (by omega) (hn j).1
  · have hcast : (j:ℤ)+1 ≤ (P:ℤ) := by exact_mod_cast j.isLt
    have hmul := mul_le_mul_of_nonneg_right hcast (show (0:ℤ) ≤ L by positivity)
    have hj := (hn j).2.1
    nlinarith
end

open scoped BigOperators
section

lemma finite_separated_subset {V : Type uV} [DecidableEq V] (C : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hsym : ∀ ⦃a b⦄, R a b → R b a) (hrefl : ∀ a, R a a) (D : ℕ)
    (hdeg : ∀ a∈C, (C.filter (R a)).card ≤ D) :
    ∃ S : Finset V, S⊆C ∧ (∀ a∈S, ∀ b∈S, a≠b → ¬R a b) ∧ C.card ≤ S.card*D := by
  classical
  let A := C.powerset.filter (fun S ↦ ∀ a∈S, ∀ b∈S, a≠b → ¬R a b)
  have hA : A.Nonempty := ⟨∅,by simp [A]⟩
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image A Finset.card hA
  simp only [A, Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSC, hsep⟩ := hS
  have hcover : C⊆S.biUnion (fun a ↦ C.filter (R a)) := by
    intro b hb
    by_contra hnot
    have hno : ∀ a∈S, ¬R a b := by
      intro a ha hab
      exact hnot (Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hb,hab⟩⟩)
    have hbS : b∉S := fun h ↦ hno b h (hrefl b)
    have hins : insert b S∈A := by
      simp only [A, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hb hSC,?_⟩
      intro a ha c hc hac
      by_cases hab : a=b
      · subst a
        have hcS : c∈S := Finset.mem_of_mem_insert_of_ne hc (Ne.symm hac)
        exact fun h ↦ hno c hcS (hsym h)
      · have haS : a∈S := Finset.mem_of_mem_insert_of_ne ha hab
        by_cases hcb : c=b
        · subst c
          exact hno a haS
        · have hcS : c∈S := Finset.mem_of_mem_insert_of_ne hc hcb
          exact hsep a haS c hcS hac
    have hle := hmax (insert b S) hins
    rw [Finset.card_insert_of_notMem hbS] at hle
    omega
  refine ⟨S,hSC,hsep,?_⟩
  calc
    C.card ≤ (S.biUnion (fun a ↦ C.filter (R a))).card := Finset.card_le_card hcover
    _ ≤ ∑ a∈S, (C.filter (R a)).card := Finset.card_biUnion_le
    _ ≤ ∑ _a∈S, D := Finset.sum_le_sum fun a ha ↦ hdeg a (hSC ha)
    _ = S.card*D := by simp


open Finset
lemma linear_filter_card (C : Finset ℤ) (a b : ℤ) (hb : b ≠ 0) (R : ℕ) :
    (C.filter (fun n => |a+b*n| ≤ (R:ℤ))).card ≤ 2*R+1 := by
  classical
  let S := C.filter (fun n => |a+b*n| ≤ (R:ℤ))
  have hinj : Function.Injective (fun n : ℤ => a+b*n) := by
    intro m n h
    exact mul_left_cancel₀ hb (add_left_cancel h)
  calc
    S.card = (S.image (fun n => a+b*n)).card := (Finset.card_image_of_injective S hinj).symm
    _ ≤ (Finset.Icc (-(R:ℤ)) R).card := by
      apply Finset.card_le_card
      intro k hk
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Icc.mpr (abs_le.mp (Finset.mem_filter.mp hn).2)
    _ = 2*R+1 := by simp; omega

lemma separated_integer_samples (C : Finset ℤ) (H R : ℕ)
    (hC : ∀ n ∈ C, (R:ℤ) < |n|) :
    ∃ S : Finset ℤ, S ⊆ C ∧
      (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ H → |v'| ≤ H → (v ≠ 0 ∨ v' ≠ 0) → (R:ℤ) < |v*n+v'*n'|) ∧
      C.card ≤ S.card*(1+(2*H+1)^2*(2*R+1)) := by
  classical
  let V : Finset ℤ := (Finset.Icc (-(H:ℤ)) H).erase 0
  let E : ℤ → ℤ → Prop := fun n n' => n=n' ∨ ∃ v ∈ V, ∃ v' ∈ V, |v*n+v'*n'| ≤ (R:ℤ)
  have hsym : ∀ ⦃n n'⦄, E n n' → E n' n := by
    intro n n' h
    rcases h with h | ⟨v,hv,v',hv',hh⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨v',hv',v,hv,by simpa [add_comm] using hh⟩
  have hcardV : V.card ≤ 2*H+1 := by
    exact (card_erase_le).trans (by simp; omega)
  have hdeg : ∀ n ∈ C, (C.filter (E n)).card ≤ 1+(2*H+1)^2*(2*R+1) := by
    intro n _
    have hsub : C.filter (E n) ⊆ {n} ∪ V.biUnion (fun v => V.biUnion (fun v' =>
        C.filter (fun n' => |v*n+v'*n'| ≤ (R:ℤ)))) := by
      intro n' hn'
      obtain ⟨hh,h⟩ := Finset.mem_filter.mp hn'
      rcases h with he | ⟨v,hv,v',hv',hne⟩
      · exact mem_union_left _ (mem_singleton.mpr he.symm)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨v,hv,mem_biUnion.mpr ⟨v',hv',Finset.mem_filter.mpr ⟨hh,hne⟩⟩⟩)
    calc
      _ ≤ ({n} ∪ V.biUnion (fun v => V.biUnion (fun v' => C.filter (fun n' => |v*n+v'*n'| ≤ (R:ℤ))))).card := Finset.card_le_card hsub
      _ ≤ 1+V.card*(V.card*(2*R+1)) := by
        apply (Finset.card_union_le _ _).trans
        simp only [Finset.card_singleton]
        apply Nat.add_le_add_left
        apply card_biUnion_le.trans
        calc
          _ ≤ ∑ v ∈ V, (V.card*(2*R+1)) := by
            apply sum_le_sum
            intro v _
            apply card_biUnion_le.trans
            calc
              _ ≤ ∑ _ ∈ V, (2*R+1) := sum_le_sum (fun v' hv' =>
                linear_filter_card C (v*n) v' (ne_of_mem_erase hv') R)
              _ = _ := by simp
          _ = _ := by simp
      _ ≤ _ := by nlinarith [Nat.mul_self_le_mul_self hcardV]
  obtain ⟨S,hSC,hs,hcard⟩ := finite_separated_subset C E hsym (fun _ => Or.inl rfl) _ hdeg
  refine ⟨S,hSC,?_,hcard⟩
  intro n hn n' hn' hne v v' hv hv' hnonzero
  by_cases hz : v=0
  · subst v
    have hv'0 : v' ≠ 0 := hnonzero.resolve_left (not_ne_iff.mpr rfl)
    have hge : (1:ℤ) ≤ |v'| := by exact Int.one_le_abs hv'0
    have hh := hC n' (hSC hn')
    simpa only [zero_mul,zero_add,abs_mul] using hh.trans_le (by nlinarith [abs_nonneg n'])
  by_cases hz' : v'=0
  · subst v'
    have hge : (1:ℤ) ≤ |v| := Int.one_le_abs hz
    have hh := hC n (hSC hn)
    simpa only [zero_mul,add_zero,abs_mul] using hh.trans_le (by nlinarith [abs_nonneg n])
  by_contra hh
  apply hs n hn n' hn' hne
  exact Or.inr ⟨v,Finset.mem_erase.mpr ⟨hz,Finset.mem_Icc.mpr (abs_le.mp hv)⟩,
    v',Finset.mem_erase.mpr ⟨hz',Finset.mem_Icc.mpr (abs_le.mp hv')⟩,le_of_not_gt hh⟩
end

section
open Set Filter
open scoped Topology

lemma separated_return_samples {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ L : ℕ, 0 < L ∧ ∀ (H R : ℕ) (Q T : ℝ),
      (R:ℝ) < Q/2 →
      (⌈Q/2⌉:ℝ) + (⌈T*(1+(2*H+1)^2*(2*R+1))⌉₊:ℝ)*L ≤ Q →
      ∃ S : Finset ℤ, T ≤ (S.card:ℝ) ∧
        (∀ n ∈ S, Q/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ Q ∧ n•(θ:CircleX) ∈ O) ∧
        (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ H → |v'| ≤ H → (v ≠ 0 ∨ v' ≠ 0) → (R:ℤ) < |v*n+v'*n'|) := by
  classical
  obtain ⟨L,hL,hret⟩ := return_samples hθ hO hne
  refine ⟨L,hL,?_⟩
  intro H R Q T hQR hlen
  let D := 1+(2*H+1)^2*(2*R+1)
  let P := ⌈T*(D:ℝ)⌉₊
  obtain ⟨C,hC,hmem⟩ := hret ⌈Q/2⌉ P
  have ha : Q/2 ≤ (⌈Q/2⌉:ℝ) := Int.le_ceil _
  have hn (n : ℤ) (hn : n∈C) : Q/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ Q ∧ n•(θ:CircleX)∈O := by
    obtain ⟨hlo,hhi,ho⟩ := hmem n hn
    refine ⟨ha.trans (by exact_mod_cast hlo),?_,ho⟩
    apply le_trans _ hlen
    exact_mod_cast hhi.le
  have hcR : ∀ n∈C, (R:ℤ) < |n| := by
    intro n hn'
    have hh : (R:ℝ)<(n:ℝ) := hQR.trans_le (hn n hn').1
    exact lt_of_lt_of_le (by exact_mod_cast hh) (le_abs_self n)
  obtain ⟨S,hSC,hsep,hcard⟩ := separated_integer_samples C H R hcR
  refine ⟨S,?_,fun n hn' => hn n (hSC hn'),hsep⟩
  have hp : T*(D:ℝ) ≤ (P:ℝ) := Nat.le_ceil _
  have hcount : (P:ℝ) ≤ (S.card:ℝ)*D := by exact_mod_cast (hC ▸ hcard)
  have hD : (0:ℝ)<D := by dsimp [D]; positivity
  exact (mul_le_mul_iff_left₀ hD).mp (hp.trans hcount)
end

open Set Filter
open scoped Topology
lemma greedy_degree_bound {m K : ℕ} (hm : 1 ≤ m) (hK : K ≤ m) :
    1+(2*m^300+1)^2*(2*(m*K*m^1000)+1) ≤ 28*m^1602 := by
  have h300 : 1 ≤ m^300 := one_le_pow₀ hm
  have h1002 : 1 ≤ m^1002 := one_le_pow₀ hm
  have h1602 : 1 ≤ m^1602 := one_le_pow₀ hm
  have hR : m*K*m^1000 ≤ m^1002 := by
    calc
      m*K*m^1000 ≤ m*m*m^1000 := by gcongr
      _ = m^1002 := by ring
  calc
    1+(2*m^300+1)^2*(2*(m*K*m^1000)+1) ≤ 1+(3*m^300)^2*(3*m^1002) := by
      gcongr  <;> omega
    _ = 1+27*m^1602 := by ring
    _ ≤ 28*m^1602 := by omega

lemma eventually_sampling_length (L K : ℕ) (hL : 0 < L) :
    ∀ᶠ m : ℕ in atTop,
      (m*K*m^1000:ℝ) < (m:ℝ)^((7:ℝ)/10*m)/2 ∧
      (⌈(m:ℝ)^((7:ℝ)/10*m)/2⌉:ℝ) +
        (⌈(m:ℝ)^((69:ℝ)/100*m)*(1+(2*m^300+1)^2*(2*(m*K*m^1000)+1))⌉₊:ℝ)*L ≤
          (m:ℝ)^((7:ℝ)/10*m) := by
  have hg := eventually_rpow_linear_gap (7/10) (69/100) (168*L) 1602 (by norm_num)
  filter_upwards [hg,eventually_ge_atTop (max 1 K)] with m hg hmK
  have hm : 1 ≤ m := (le_max_left _ _).trans hmK
  have hK : K ≤ m := (le_max_right _ _).trans hmK
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0:ℝ) < m := lt_of_lt_of_le zero_lt_one hx
  let T : ℝ := (m:ℝ)^((69:ℝ)/100*m)
  let Q : ℝ := (m:ℝ)^((7:ℝ)/10*m)
  let D : ℝ := 1+(2*(m:ℝ)^300+1)^2*(2*((m:ℝ)*K*(m:ℝ)^1000)+1)
  have hT : 1 ≤ T := Real.one_le_rpow hx (by positivity)
  have hD : 1 ≤ D := by dsimp [D]; exact le_add_of_nonneg_right (by positivity)
  have hL' : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hdegree : D ≤ 28*(m:ℝ)^1602 := by
    have hh : ((1+(2*m^300+1)^2*(2*(m*K*m^1000)+1):ℕ):ℝ) ≤ ((28*m^1602:ℕ):ℝ) := Nat.cast_le.mpr (greedy_degree_bound hm hK)
    simpa only [D, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hh
  have hg' : 168*(L:ℝ)*(m:ℝ)^1602*T ≤ Q := by
    simpa only [Real.rpow_ofNat] using hg
  have hTDL : 6*(T*D*L) ≤ Q := by
    calc
      6*(T*D*L) ≤ 6*(T*(28*(m:ℝ)^1602)*L) := by gcongr
      _ = 168*(L:ℝ)*(m:ℝ)^1602*T := by ring
      _ ≤ Q := hg'
  have hR : (m:ℝ)*K*(m:ℝ)^1000 ≤ (m:ℝ)^1602 := by
    have hK' : (K:ℝ) ≤ m := Nat.cast_le.mpr hK
    calc
      (m:ℝ)*K*(m:ℝ)^1000 ≤ (m:ℝ)*(m:ℝ)*(m:ℝ)^1000 := by gcongr
      _ = (m:ℝ)^1002 := by ring
      _ ≤ (m:ℝ)^1602 := pow_le_pow_right₀ hx (by omega)
  have hp : (0:ℝ) < (m:ℝ)^1602 := by positivity
  have hQ : 6*(m:ℝ)^1602 ≤ Q := by
    calc
      6*(m:ℝ)^1602 ≤ 168*(L:ℝ)*(m:ℝ)^1602*1 := by nlinarith
      _ ≤ 168*(L:ℝ)*(m:ℝ)^1602*T := by gcongr
      _ ≤ Q := hg'
  refine ⟨by dsimp [Q] at hQ; nlinarith,?_⟩
  change (⌈Q/2⌉:ℝ)+(⌈T*D⌉₊:ℝ)*L ≤ Q
  have hceilQ : (⌈Q/2⌉:ℝ) ≤ Q/2+1 := (Int.ceil_lt_add_one _).le
  have hceilT : (⌈T*D⌉₊:ℝ) ≤ T*D+1 := (Nat.ceil_lt_add_one (show 0 ≤ T*D by positivity)).le
  have hTD : 1 ≤ T*D := one_le_mul_of_one_le_of_one_le hT hD
  have hTDL1 : (L:ℝ) ≤ T*D*L := by nlinarith
  have hbound := mul_le_mul_of_nonneg_right hceilT (show (0:ℝ) ≤ L by positivity)
  nlinarith

lemma eventually_separated_returns {θ : ℝ} (hθ : Irrational θ) {O : Set CircleX}
    (hO : IsOpen O) (hne : O.Nonempty) (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∃ S : Finset ℤ,
      (m:ℝ)^((69:ℝ)/100*m) ≤ (S.card:ℝ) ∧
      (∀ n ∈ S, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ (n:ℝ) ∧
        (n:ℝ) ≤ (m:ℝ)^((7:ℝ)/10*m) ∧ n•(θ:CircleX)∈O) ∧
      (∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ m^300 → |v'| ≤ m^300 → (v ≠ 0 ∨ v' ≠ 0) →
          (m*K*m^1000:ℤ) < |v*n+v'*n'|) := by
  obtain ⟨L,hL,hs⟩ := separated_return_samples hθ hO hne
  filter_upwards [eventually_sampling_length L K hL] with m hm
  have hh := hs (m^300) (m*K*m^1000) ((m:ℝ)^((7:ℝ)/10*m)) ((m:ℝ)^((69:ℝ)/100*m))
    (by simpa only [Nat.cast_mul, Nat.cast_pow] using hm.1)
    (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hm.2)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hh


end CircleSampling

end

end OAI
