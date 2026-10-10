import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.CountableArraySaturation
import OAI.Analysis.JiangSu.Traceless.TracelessCanonicalPure

namespace OAI


noncomputable section
namespace CurrentMain.Traceless
open Pureness DirectComparison PureStateExcision Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem finite_scalar_cross_excision (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : EmptyTraceComparison A)
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hpure : ofPositiveState φ hφ∈(realStateCarrier (A := A)).extremePoints ℝ)
    {I K : Type} [Fintype I] [Fintype K] [DecidableEq K] (a : I→A) {ε : ℝ} (hε : 0<ε) :
    ∃ z : K→A,(∀ i j,star (z i)*z j=if i=j then 1 else 0) ∧
      (∀ i,‖z i‖≤1) ∧ ∀ i j l,
        ‖star (z i)*a l*z j-(if i=j then φ (a l) • (1:A) else 0)‖<ε := by
  classical
  let c : I→A := fun i=>a i-φ (a i) • (1:A)
  let C : ℝ := (∑ i,‖c i‖)+1
  have hC1 : 1≤C := by
    have hs : 0≤∑ i,‖c i‖ := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
    dsimp [C]; linarith
  have hC : 0<C := lt_of_lt_of_le zero_lt_one hC1
  have hc (l : I) : ‖c l‖≤C := by
    have := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset I))=>norm_nonneg (c i))
      (Finset.mem_univ l)
    dsimp [C]; linarith
  let δ := min (1/2 : ℝ) (ε/(8*C))
  have hδ : 0<δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ≤1 := (min_le_left _ _).trans (by norm_num)
  have hδε : 2*C*δ≤ε/4 := by
    have hh := (le_div_iff₀ (show 0<8*C by positivity)).mp (min_le_right (1/2 : ℝ) (ε/(8*C)))
    change δ*(8*C)≤ε at hh
    nlinarith
  obtain ⟨g,hg,hgn,hgφ,hga⟩ := pure_state_finite_excision φ hφ hpure a
    (show 0<ε/2 by positivity) hδ
  let b := directPositiveCut (1-δ) g
  have hb : 0≤b := directPositiveCut_nonneg _ _
  have hb0 : b≠0 := high_cut_ne_zero φ hφ hg hδ1 hgφ
  obtain ⟨w,hw,_hp,hwm⟩ := exists_hereditary_isometry_range hb
    (unit_cuntz_of_empty_comparison hcmp hb hb0)
  have hgw : ‖g*w-w‖≤δ := isometry_peak_bound hg hgn hδ.le hw hwm
  obtain ⟨u,v,hu,hv,huv⟩ := exists_two_isometries hsimple hinf hcmp
  obtain ⟨r,hr⟩ := finite_isometries_of_two hu hv huv (Fintype.card K)
  let z : K→A := fun i=>w*r (Fintype.equivFin K i)
  have hz (i j : K) : star (z i)*z j=if i=j then 1 else 0 := by
    dsimp [z]
    rw [star_mul]
    calc
      _=star (r (Fintype.equivFin K i))*(star w*w)*r (Fintype.equivFin K j) := by noncomm_ring
      _=if i=j then 1 else 0 := by rw [hw,mul_one,hr]; simp
  have hzn (i : K) : ‖z i‖=1 := isometry_norm_one (by simpa using hz i i)
  have hgz (i : K) : ‖g*z i-z i‖≤δ := by
    have he : g*z i-z i=(g*w-w)*r (Fintype.equivFin K i) := by dsimp [z]; noncomm_ring
    rw [he]
    calc
      _≤‖g*w-w‖*‖r (Fintype.equivFin K i)‖ := norm_mul_le _ _
      _≤δ := by
        have hn := isometry_norm_one (w := r (Fintype.equivFin K i))
          (by simpa using hr (Fintype.equivFin K i) (Fintype.equivFin K i))
        rw [hn,mul_one]
        exact hgw
  refine ⟨z,hz,fun i=>(hzn i).le,fun i j l=>?_⟩
  have hgc : g*c l*g=g*a l*g-φ (a l) • (g*g) := by
    dsimp [c]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one]
  have he : star (z i)*c l*z j=star (z i)*a l*z j-
      (if i=j then φ (a l) • (1:A) else 0) := by
    dsimp [c]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,hz]
    split_ifs <;> simp
  rw [←he]
  have hh := cross_compression_bound hg.isSelfAdjoint hgn (hzn i).le (hzn j).le hδ.le
    (hgz i) (hgz j) (c := c l)
  rw [hgc] at hh
  have hmul : 2*‖c l‖*δ≤2*C*δ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hc l) (by norm_num)) hδ.le
  have ha := hga l
  linarith

variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

theorem scalar_cross_excision_ultrapower (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : EmptyTraceComparison A)
    (hfree : (U : Filter ℕ)≤atTop)
    (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hpure : ofPositiveState φ hφ∈(realStateCarrier (A := A)).extremePoints ℝ) :
    ∃ z : ℕ→N,(∀ i,‖z i‖≤1) ∧
      ∀ i j a,star (z i)*ι a*z j=if i=j then φ a • (1:N) else 0 := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let b : Option ℕ→A | none=>1 | some n=>a n
  let g : (ℕ×ℕ×Option ℕ)→ℕ→(ℕ→A)→ℝ := fun t _ x=>
    ‖star (x t.1)*b t.2.2*x t.2.1-(if t.1=t.2.1 then φ (b t.2.2) • (1:A) else 0)‖
  have hs (F : Finset (ℕ×ℕ×Option ℕ)) (ε : ℝ) (hε : 0<ε) :
      ∀ᶠ k in (U : Filter ℕ),∃ x : ℕ→A,(∀ i,‖x i‖≤1) ∧ ∀ j∈F,g j k x<ε := by
    let M := F.sup (fun j=>max j.1 j.2.1)
    obtain ⟨v,hv,hvn,hva⟩ := finite_scalar_cross_excision hsimple hinf hcmp φ hφ hpure
      (K := Fin (M+1)) (fun t : F=>b t.val.2.2) hε
    let x : ℕ→A := fun i=>if h:i≤M then v ⟨i,by omega⟩ else 0
    apply Filter.Eventually.of_forall
    intro k
    refine ⟨x,fun i=>?_,fun t ht=>?_⟩
    · dsimp [x]
      split_ifs <;> simp_all
    · have htM : max t.1 t.2.1≤M := Finset.le_sup (f := fun j : ℕ×ℕ×Option ℕ=>max j.1 j.2.1) ht
      have hi : t.1≤M := (le_max_left _ _).trans htM
      have hj : t.2.1≤M := (le_max_right _ _).trans htM
      have hh := hva ⟨t.1,by omega⟩ ⟨t.2.1,by omega⟩ ⟨t,ht⟩
      simpa only [g,x,dite_eq_left hi,dite_eq_left hj,Fin.mk.injEq] using hh
  obtain ⟨x,hxn,hx⟩ := NormUltra.bounded_countable_array_test U hfree
    (fun _ : ℕ=>(1:ℝ)) (fun _=>zero_le_one) g (fun _ _ _=>norm_nonneg _) hs
  let z : ℕ→N := fun i=>NormUltra.QuotientAlgebra.mk U (x i)
  have hzb (i j : ℕ) (k : Option ℕ) :
      star (z i)*ι (b k)*z j=if i=j then φ (b k) • (1:N) else 0 := by
    have he : star (z i)*ι (b k)*z j=
        ι (if i=j then φ (b k) • (1:A) else 0) := by
      exact (NormUltra.QuotientAlgebra.mk_eq_mk_iff
        (star (x i)*boundedDiagonal (b k)*x j)
        (boundedDiagonal (if i=j then φ (b k) • (1:A) else 0))).mpr (hx (i,j,k))
    rw [he]
    split_ifs <;> simp [normInclusion_one]
  refine ⟨z,fun i=>?_,fun i j c=>?_⟩
  · exact (NormUltra.QuotientAlgebra.norm_mk_le (x i)).trans
      (lp.norm_le_of_forall_le zero_le_one (hxn i))
  · have h1 : Continuous (fun c : A=>star (z i)*ι c*z j) := by fun_prop
    have h2 : Continuous (fun c : A=>if i=j then φ c • (1:N) else 0) := by
      split_ifs <;> fun_prop
    exact congrFun (ha.equalizer h1 h2 (funext fun n=>hzb i j (some n))) c

end CurrentMain.Traceless


namespace CStarExcision
open NuclearNorm
open scoped ComplexOrder

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NonUnitalCStarAlgebra B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma stateRowElement_mutual_cross (ρ : A →⋆ₙₐ[ℂ] B) (R S : StateRow (A := A))
    (v z : B) (hz : ∀ a,star v*ρ a*z=0) (a : A) :
    star (stateRowElement ρ R v)*ρ a*stateRowElement ρ S z=0 := by
  simp only [stateRowElement,assembled,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro i _
  calc
    _=star (ρ (R.right i))*(star v*ρ (star (R.left i)*a*S.left j)*z)*ρ (S.right j) := by
      simp only [map_mul,map_star]
      noncomm_ring
    _=0 := by rw [hz,mul_zero,zero_mul]

lemma stateRowSum_eq_sum (φ : A →ₚ[ℂ] ℂ) (R : List (StateRow (A := A))) (a : selfAdjoint A) :
    (stateRowSum φ R a : A)=∑ j : Fin R.length,((R.get j).map φ a : A) := by
  induction R with
  | nil => simp [stateRowSum]
  | cons r R ih =>
    simp only [List.length_cons] at *
    rw [Fin.sum_univ_succ]
    change (r.map φ a : A)+(stateRowSum φ R a : A)=(r.map φ a : A)+_
    rw [ih]
    rfl

end CStarExcision
namespace CurrentMain.Traceless
open Pureness DirectComparison PureStateExcision NuclearNorm CStarExcision Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

omit [Nontrivial A] [TopologicalSpace.SeparableSpace A] in
theorem nuclear_cross_assembly (φ : A →ₚ[ℂ] ℂ)
    (z : ℕ→N) (hz : ∀ i j a,star (z i)*ι a*z j=if i=j then φ a • (1:N) else 0)
    (R : List (StateRow (A := A))) :
    ∃ v : ℕ→N,∀ g h (a : selfAdjoint A),
      star (v g)*ι (a:A)*v h=if g=h then ι (stateRowSum φ R a : A) else 0 := by
  classical
  let w (g : ℕ) (j : Fin R.length) : N := stateRowElement ι (R.get j) (z (Nat.pair g j))
  have hdiag (g : ℕ) (j : Fin R.length) (a : selfAdjoint A) :
      star (w g j)*ι (a:A)*w g j=ι ((R.get j).map φ a : A) := by
    have hh := stateRowElement_compress ι (R.get j) φ (z (Nat.pair g j)) 1
      (fun _=>by simp) (fun b=>by simpa using hz (Nat.pair g j) (Nat.pair g j) b) a
    simpa only [mul_one] using hh
  have hcross (g h : ℕ) (j k : Fin R.length) (hneq : g≠h ∨ j≠k) (a : A) :
      star (w g j)*ι a*w h k=0 := by
    apply stateRowElement_mutual_cross
    intro b
    rw [hz,ite_eq_right]
    intro he
    have hh := Nat.pair_eq_pair.mp he
    rcases hneq with hneq|hneq
    · exact hneq hh.1
    · exact hneq (Fin.ext hh.2)
  let v : ℕ→N := fun g=>∑ j,w g j
  refine ⟨v,fun g h a=>?_⟩
  have he : star (v g)*ι (a:A)*v h=∑ j,∑ k,star (w g j)*ι (a:A)*w h k := by
    simp only [v,star_sum,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  by_cases hgh : g=h
  · subst h
    rw [ite_eq_left rfl, stateRowSum_eq_sum,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single j]
    · exact hdiag g j a
    · intro k _ hkj
      exact hcross g g j k (Or.inr hkj.symm) a
    · simp
  · rw [ite_eq_right hgh]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    exact hcross g h j k (Or.inl hgh) a

end CurrentMain.Traceless

end

end OAI
