import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.RationalStarHomExtension
import OAI.Analysis.JiangSu.CuntzSemigroup.RationalTerms

namespace OAI

section

noncomputable section
namespace NormUltra
open Filter Topology
open scoped ENNReal

variable {A : Type*} [NormedAddCommGroup A]

 theorem bounded_array_test (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
    (C : ℕ→ℝ) (hC : ∀ i,0≤C i) (g : ℕ→ℕ→(ℕ→A)→ℝ)
    (hg : ∀ j k x,0≤g j k x)
    (hsupply : ∀ m : ℕ,∀ ε : ℝ,0<ε → ∀ᶠ k in (U : Filter ℕ),
      ∃ x : ℕ→A,(∀ i,‖x i‖≤C i) ∧ ∀ j ≤ m,g j k x<ε) :
    ∃ x : ℕ→lp (fun _ : ℕ=>A) ∞,(∀ i k,‖x i k‖≤C i) ∧
      ∀ j,Tendsto (fun k=>g j k (fun i=>x i k)) (U : Filter ℕ) (𝓝 0) := by
   classical
   let ε : ℕ→ℝ := fun m=>1/((m:ℝ)+1)
   have hε (m : ℕ) : 0<ε m := by dsimp [ε]; positivity
   have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
   let P : ℕ→ℕ→Prop := fun m k=>∃ x : ℕ→A,(∀ i,‖x i‖≤C i) ∧ ∀ j ≤ m,g j k x<ε m
   have hP (m : ℕ) : ∀ᶠ k in (U : Filter ℕ),P m k := hsupply m (ε m) (hε m)
   obtain ⟨j,hj,hjP⟩ := NonunitalGamma.kernel_diagonal_choice U hfree P hP
   let y : ℕ→ℕ→A := fun k=>if h:P (j k) k then h.choose else fun _=>0
   have hyn (i k : ℕ) : ‖y k i‖≤C i := by
     dsimp [y]
     split_ifs with h
     · exact h.choose_spec.1 i
     · simpa only [norm_zero] using hC i
   let x : ℕ→lp (fun _ : ℕ=>A) ∞ := fun i=>⟨fun k=>y k i,
      memℓp_infty ⟨C i,by rintro _ ⟨k,rfl⟩; exact hyn i k⟩⟩
   refine ⟨x,hyn,?_⟩
   intro i
   apply squeeze_zero' (Eventually.of_forall fun k=>hg i k (fun z=>x z k)) _ (hε0.comp hj)
   filter_upwards [hjP,hj (eventually_ge_atTop i)] with k hk hki
   change g i k (y k)≤ε (j k)
   dsimp [y]
   rw [dite_eq_left hk]
   exact (hk.choose_spec.2 i hki).le
 theorem bounded_array_test_countable {J : Type*} [Countable J] [Nonempty J]
    (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
    (C : ℕ→ℝ) (hC : ∀ i,0≤C i) (g : J→ℕ→(ℕ→A)→ℝ)
    (hg : ∀ j k x,0≤g j k x)
    (hsupply : ∀ F : Finset J,∀ ε : ℝ,0<ε → ∀ᶠ k in (U : Filter ℕ),
      ∃ x : ℕ→A,(∀ i,‖x i‖≤C i) ∧ ∀ j∈F,g j k x<ε) :
    ∃ x : ℕ→lp (fun _ : ℕ=>A) ∞,(∀ i k,‖x i k‖≤C i) ∧
      ∀ j,Tendsto (fun k=>g j k (fun i=>x i k)) (U : Filter ℕ) (𝓝 0) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat J
  obtain ⟨x,hxn,hx⟩ := bounded_array_test U hfree C hC (fun j=>g (e j))
    (fun j=>hg (e j)) (fun m ε hε=>by
      filter_upwards [hsupply ((Finset.range (m+1)).image e) ε hε] with k ⟨x,hxn,hx⟩
      exact ⟨x,hxn,fun j hj=>hx (e j) (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩)⟩)
  exact ⟨x,hxn,fun j=>by obtain ⟨i,rfl⟩:=he j; exact hx i⟩
end NormUltra

end
end

section

noncomputable section
namespace NormUltra
open Filter Topology DirectComparison RationalTerms QuotientAlgebra
open scoped ENNReal CStarAlgebra

local instance rationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
variable {D A : Type*} [CStarAlgebra D] [CStarAlgebra A]
variable (U : Ultrafilter ℕ) (d : ℕ→D)
local notation "N" => QuotientAlgebra (fun _ : ℕ=>A) U
local notation "L" => lp (fun _ : ℕ=>A) ∞

 def CentralFiniteModels : Prop :=
   ∀ F : Finset (Term ℕ),∃ w : ℕ→N,
     (∀ j,‖w j‖≤‖d j‖) ∧ (∀ a j,Commute (diagonalHom U a) (w j)) ∧
     w 0=algebraMap ℂ N Complex.I ∧ ∀ e∈F,‖e.eval w‖≤‖e.eval d‖

 abbrev Test := Term ℕ ⊕ ((ℕ×ℕ) ⊕ Unit)
 instance : Nonempty Test := ⟨.inl (.scalar 0)⟩
 def testValue (a : ℕ→A) : Test→(ℕ→A)→ℝ
 | .inl e,x => max (‖e.eval x‖-‖e.eval d‖) 0
 | .inr (.inl (i,j)),x => ‖a i*x j-x j*a i‖
 | .inr (.inr _),x => ‖x 0-algebraMap ℂ A Complex.I‖
lemma testValue_nonneg (a : ℕ→A) (t : Test) (x : ℕ→A) : 0≤testValue d a t x := by
  rcases t with e | (⟨i,j⟩ | u)
  · exact le_max_right _ _
  · exact norm_nonneg _
  · exact norm_nonneg _

 theorem central_rational_saturation [TopologicalSpace.SeparableSpace A]
    (hfree : (U : Filter ℕ)≤atTop) (hd : DenseRange d)
    (hdI : d 0=algebraMap ℂ D Complex.I) (hmodels : CentralFiniteModels (A := A) U d) :
    ∃ φ : D →⋆ₐ[ℂ] N,∀ a z,Commute (diagonalHom U a) (φ z) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  have hs (F : Finset Test) (ε : ℝ) (hε : 0<ε) : ∀ᶠ k in (U : Filter ℕ),
      ∃ x : ℕ→A,(∀ j,‖x j‖≤‖d j‖+1) ∧ ∀ t∈F,testValue d a t x<ε := by
    let E : Finset (Term ℕ) := F.biUnion (fun t=>match t with | .inl e=>{e} | _=>∅)
    obtain ⟨w,hwn,hwc,hwI,hwe⟩ := hmodels E
    choose x hx hxn using (fun j=>exists_norm_mk_lt (w j) zero_lt_one)
    have ht (t : Test) (ht : t∈F) : ∀ᶠ k in (U : Filter ℕ),
        testValue d a t (fun j=>x j k)<ε := by
      rcases t with e | (⟨i,j⟩ | u)
      · have he : e∈E := Finset.mem_biUnion.mpr ⟨.inl e,ht,Finset.mem_singleton_self e⟩
        have hn : ‖mk U (e.boundedEval x)‖<‖e.eval d‖+ε := by
          rw [e.mk_boundedEval]
          simp_rw [hx]
          exact (hwe e he).trans_lt (lt_add_of_pos_right _ hε)
        filter_upwards [NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ hn] with k hk
        rw [e.boundedEval_apply] at hk
        exact max_lt_iff.mpr ⟨by linarith,hε⟩
      · have hn : ‖mk U (boundedDiagonal (a i)*x j-x j*boundedDiagonal (a i))‖<ε := by
          change ‖diagonalHom U (a i)*mk U (x j)-mk U (x j)*diagonalHom U (a i)‖<ε
          rw [hx,(hwc (a i) j).eq,sub_self,norm_zero]
          exact hε
        exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ hn
      · have hn : ‖mk U (x 0-boundedDiagonal (algebraMap ℂ A Complex.I))‖<ε := by
          change ‖mk U (x 0)-diagonalHom U (algebraMap ℂ A Complex.I)‖<ε
          rw [hx,hwI]
          have hi : diagonalHom U (algebraMap ℂ A Complex.I)=algebraMap ℂ N Complex.I :=
            (diagonalHom U).commutes Complex.I
          rw [hi,sub_self,norm_zero]
          exact hε
        exact NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U _ hn
    filter_upwards [(eventually_all_finset F).mpr ht] with k hk
    refine ⟨fun j=>x j k,fun j=>?_,hk⟩
    exact ((BoundedFamilies.norm_coordinate_le (x j) k).trans (hxn j).le).trans (by linarith [hwn j])
  obtain ⟨x,_hxn,hx⟩ := bounded_array_test_countable U hfree (fun j=>‖d j‖+1)
    (fun j=>by positivity) (fun t _=>testValue d a t) (fun t _=>testValue_nonneg d a t) hs
  let w : ℕ→N := fun j=>mk U (x j)
  have hnorm (e : Term ℕ) : ‖e.eval w‖≤‖e.eval d‖ := by
    rw [←e.mk_boundedEval x U,norm_mk_eq_limsup]
    apply le_of_forall_pos_le_add
    intro ε hε
    apply limsup_le_of_le (BoundedFamilies.norm_cobounded U (e.boundedEval x))
    have ht := (tendsto_order.mp (hx (.inl e))).2 ε hε
    filter_upwards [ht] with k hk
    rw [e.boundedEval_apply]
    have hh : ‖e.eval (fun j=>x j k)‖-‖e.eval d‖≤
        max (‖e.eval (fun j=>x j k)‖-‖e.eval d‖) 0 := le_max_left _ _
    change max (‖e.eval (fun j=>x j k)‖-‖e.eval d‖) 0<ε at hk
    linarith
  have hwc (b : A) (j : ℕ) : Commute (diagonalHom U b) (w j) := by
    have he (i : ℕ) : diagonalHom U (a i)*w j=w j*diagonalHom U (a i) :=
      (mk_eq_mk_iff (boundedDiagonal (a i)*x j) (x j*boundedDiagonal (a i))).mpr
        (hx (.inr (.inl (i,j))))
    exact ha.induction_on b (isClosed_eq
      ((map_continuous (diagonalHom U : A →⋆ₐ[ℂ] N)).mul continuous_const)
      (continuous_const.mul (map_continuous (diagonalHom U : A →⋆ₐ[ℂ] N)))) he
  have hwI : w 0=algebraMap ℂ N Complex.I := by
    have h := (mk_eq_mk_iff (x 0) (boundedDiagonal (algebraMap ℂ A Complex.I))).mpr
      (hx (.inr (.inr ())))
    exact h.trans ((diagonalHom U).commutes _)
  have hS : Dense (evalRange d : Set D) := hd.mono (by rintro z ⟨j,rfl⟩; exact ⟨.gen j,rfl⟩)
  have hI : algebraMap ℂ D Complex.I∈evalRange d := ⟨.gen 0,hdI⟩
  let f := RationalTerms.lift d w hnorm
  have hfI : f ⟨algebraMap ℂ D Complex.I,hI⟩=algebraMap ℂ N Complex.I := by
    exact (liftedValue_eq d w hnorm ⟨algebraMap ℂ D Complex.I,hI⟩ (.gen 0) hdI).trans hwI
  let φ := RationalStarExtension.extension (evalRange d) hS f
    (RationalTerms.lift_norm d w hnorm) hI hfI
  have hφ (j : ℕ) : φ (d j)=w j := by
    have he := RationalStarExtension.extension_eq (evalRange d) hS f
      (RationalTerms.lift_norm d w hnorm) hI hfI ⟨d j,⟨.gen j,rfl⟩⟩
    exact he.trans (liftedValue_eq d w hnorm _ (.gen j) rfl)
  refine ⟨φ,fun b z=>?_⟩
  show diagonalHom U b*φ z=φ z*diagonalHom U b
  refine hd.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_const.mul (map_continuous φ)) ((map_continuous φ).mul continuous_const)
  · intro j
    rw [hφ]
    exact (hwc b j).eq
end NormUltra

end
end

end OAI
