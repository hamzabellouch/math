import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traceless.TracelessFiniteScalarExcision

namespace OAI


noncomputable section
namespace CurrentMain.Traceless
open Pureness DirectComparison PureStateExcision NuclearNorm CStarExcision Filter Topology
open scoped ComplexOrder ComplexStarModule ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

theorem finite_identity_cross_excision (hnuc : IsNuclear.{0,0} A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : EmptyTraceComparison A) (hfree : (U : Filter ℕ)≤atTop)
    {I : Type} [Fintype I] (a : I→selfAdjoint A) {ε : ℝ} (hε : 0<ε) :
    ∃ v : ℕ→N,(∀ i,‖v i‖≤2) ∧ ∀ g h i,
      ‖star (v g)*ι (a i : A)*v h-(if g=h then ι (a i : A) else 0)‖<ε := by
  classical
  obtain ⟨φ,hφ,hpure⟩ := exists_pure_positive_state (A := A)
  obtain ⟨z,_hzn,hz⟩ := scalar_cross_excision_ultrapower U hsimple hinf hcmp hfree φ hφ hpure
  let b : Option I→selfAdjoint A | none=>1 | some i=>a i
  let δ := min ε 1
  have hδ : 0<δ := lt_min hε zero_lt_one
  obtain ⟨R,hR⟩ := simple_nuclear_state_coefficient_approximation hnuc hsimple φ hφ b hδ
  obtain ⟨v,hv⟩ := nuclear_cross_assembly U φ z hz R
  have herr (g : ℕ) (i : Option I) :
      ‖star (v g)*ι (b i : A)*v g-ι (b i : A)‖<δ := by
    rw [hv,ite_eq_left rfl,←map_sub]
    calc
      _≤‖(stateRowSum φ R (b i) : A)-(b i : A)‖ := NonUnitalStarAlgHom.norm_apply_le ι _
      _=‖b i-stateRowSum φ R (b i)‖ := by rw [norm_sub_rev]; rfl
      _≤‖b-fun i=>stateRowSum φ R (b i)‖ := norm_le_pi_norm (b-fun i=>stateRowSum φ R (b i)) i
      _<δ := hR
  have hvn (g : ℕ) : ‖v g‖≤2 := by
    have he : ‖star (v g)*v g-(1:N)‖<δ := by
      simpa only [b,selfAdjoint.val_one,normInclusion_one,mul_one] using herr g none
    have hs : ‖star (v g)*v g‖=‖v g‖*‖v g‖ := CStarRing.norm_star_mul_self
    have hh := norm_le_norm_sub_add (star (v g)*v g) (1:N)
    have hδ1 : δ≤1 := min_le_right _ _
    have hone : ‖(1:N)‖≤1 := by
      by_cases h : Nontrivial N
      · let := h; simp
      · let := not_nontrivial_iff_subsingleton.mp h; simp [Subsingleton.elim (1:N) 0]
    nlinarith [norm_nonneg (v g)]
  refine ⟨v,hvn,fun g h i=>?_⟩
  by_cases he : g=h
  · subst h
    rw [ite_eq_left rfl]
    exact (herr g (some i)).trans_le (min_le_left _ _)
  · rw [hv,ite_eq_right he,ite_eq_right he,sub_self,norm_zero]
    exact hε


theorem identity_cross_excision_ultrapower (hnuc : IsNuclear.{0,0} A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : EmptyTraceComparison A) (hfree : (U : Filter ℕ)≤atTop) :
    ∃ x : ℕ→lp (fun _ : ℕ=>A) ∞,(∀ i k,‖x i k‖≤3) ∧
      let z := fun i=>NormUltra.QuotientAlgebra.mk U (x i)
      (∀ i j a,star (z i)*ι a*z j=if i=j then ι a else 0) ∧
      (∀ i,star (z i)*z i=1) ∧ (∀ i a,Commute (z i) (ι a)) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq (selfAdjoint A)
  let b : Option ℕ→selfAdjoint A | none=>1 | some n=>a n
  let g : (ℕ×ℕ×Option ℕ)→ℕ→(ℕ→A)→ℝ := fun t _ x=>
    ‖star (x t.1)*(b t.2.2 : A)*x t.2.1-(if t.1=t.2.1 then (b t.2.2 : A) else 0)‖
  have hs (F : Finset (ℕ×ℕ×Option ℕ)) (ε : ℝ) (hε : 0<ε) :
      ∀ᶠ k in (U : Filter ℕ),∃ x : ℕ→A,(∀ i,‖x i‖≤3) ∧ ∀ j∈F,g j k x<ε := by
    obtain ⟨v,hvn,hv⟩ := finite_identity_cross_excision U hnuc hsimple hinf hcmp hfree
      (fun t : F=>b t.val.2.2) hε
    choose x hx hxn using (fun i=>NormUltra.QuotientAlgebra.exists_norm_mk_lt (v i) zero_lt_one)
    have hq (t : F) :
        ‖NormUltra.QuotientAlgebra.mk U (star (x t.val.1)*boundedDiagonal (b t.val.2.2 : A)*x t.val.2.1-
          boundedDiagonal (if t.val.1=t.val.2.1 then (b t.val.2.2 : A) else 0))‖<ε := by
      change ‖star (NormUltra.QuotientAlgebra.mk U (x t.val.1))*ι (b t.val.2.2 : A)*
        NormUltra.QuotientAlgebra.mk U (x t.val.2.1)-
          ι (if t.val.1=t.val.2.1 then (b t.val.2.2 : A) else 0)‖<ε
      simpa only [hx,apply_ite,map_zero] using hv t.val.1 t.val.2.1 t
    have hh : ∀ᶠ k in (U : Filter ℕ),∀ t : F,g t.val k (fun i=>x i k)<ε := by
      exact Filter.eventually_all.2 (fun t=>
        NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ (hq t))
    filter_upwards [hh] with k hk
    refine ⟨fun i=>x i k,fun i=>?_,fun t ht=>hk ⟨t,ht⟩⟩
    exact ((NormUltra.BoundedFamilies.norm_coordinate_le (x i) k).trans (hxn i).le).trans (by linarith [hvn i])
  obtain ⟨x,hxn,hx⟩ := NormUltra.bounded_countable_array_test U hfree
    (fun _ : ℕ=>(3:ℝ)) (fun _=>by norm_num) g (fun _ _ _=>norm_nonneg _) hs
  let z : ℕ→N := fun i=>NormUltra.QuotientAlgebra.mk U (x i)
  have hzb (i j : ℕ) (k : Option ℕ) :
      star (z i)*ι (b k : A)*z j=if i=j then ι (b k : A) else 0 := by
    have he : star (z i)*ι (b k : A)*z j=ι (if i=j then (b k : A) else 0) := by
      exact (NormUltra.QuotientAlgebra.mk_eq_mk_iff
        (star (x i)*boundedDiagonal (b k : A)*x j)
        (boundedDiagonal (if i=j then (b k : A) else 0))).mpr (hx (i,j,k))
    rw [he]
    split_ifs <;> simp
  have hsa (i j : ℕ) (c : selfAdjoint A) :
      star (z i)*ι (c:A)*z j=if i=j then ι (c:A) else 0 := by
    have hc1 : Continuous (fun c : selfAdjoint A=>star (z i)*ι (c:A)*z j) := by fun_prop
    have hc2 : Continuous (fun c : selfAdjoint A=>if i=j then ι (c:A) else 0) := by
      split_ifs <;> fun_prop
    exact congrFun (ha.equalizer hc1 hc2 (funext fun n=>hzb i j (some n))) c
  have hz (i j : ℕ) (c : A) : star (z i)*ι c*z j=if i=j then ι c else 0 := by
    conv_lhs => rw [←realPart_add_I_smul_imaginaryPart c]
    rw [map_add,map_smul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,hsa,hsa]
    split_ifs with he
    · rw [←map_smul,←map_add,realPart_add_I_smul_imaginaryPart]
    · simp
  have hz1 (i : ℕ) : star (z i)*z i=1 := by
    simpa [normInclusion_one] using hz i i 1
  refine ⟨x,hxn,hz,hz1,fun i c=>?_⟩
  apply CStarExcision.commute_of_excision (z i) 1 (ι c) (hz1 i)
  · simpa using hz i i c
  · simpa only [eq_self,ite_true,mul_one,map_star] using hz i i (star c)
  · simpa only [eq_self,ite_true,mul_one,map_star,map_mul] using hz i i (star c*c)

end CurrentMain.Traceless

end

end OAI
