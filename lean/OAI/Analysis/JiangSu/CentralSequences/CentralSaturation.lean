import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.CountableArraySaturation

namespace OAI

section

noncomputable section
namespace NonunitalCentralSaturation
open Filter Topology NormUltra NormUltra.QuotientAlgebra NonunitalGamma RationalTerms
open scoped ENNReal CStarAlgebra

local instance saturationRationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
variable {D A : Type} [CStarAlgebra D] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ) [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ)≤atTop)]
local notation "N" => QuotientAlgebra (fun _ : ℕ=>A) U
local notation "C" => normCentralizer (A := A) U
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local notation "L" => lp (fun _ : ℕ=>A) ∞
local notation "π" => centralSequenceQuotient (A := A) U
local notation "cu" => centralLocalUnit (A := A) U

theorem rational_saturation (d : ℕ→D) (hd : DenseRange d)
    (hdI : d 0=algebraMap ℂ D Complex.I) (hmodels : FiniteModels (A := A) U d) :
    Nonempty (D →⋆ₐ[ℂ] Fω) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨u,hu⟩ := QuotientAlgebra.mk_surjective (cu:N)
  obtain ⟨x,_hxn,hx⟩ := bounded_countable_array_test U (Fact.out : (U : Filter ℕ)≤atTop)
    (fun v=>baseBound d v+1) (fun v=>by have := baseBound_nonneg d v; linarith)
    (fun t k=>testValue d a (u k) t) (fun t k=>testValue_nonneg d a (u k) t)
    (fun F ε hε=>finite_models_coordinate_supply U d a u hu hmodels F hε)
  have hc (v : Var) : mk U (x v)∈C := by
    intro b
    have he (i : ℕ) : mk U (x v)*normInclusion U (a i)=normInclusion U (a i)*mk U (x v) := by
      have h := (mk_eq_mk_iff (x v*boundedConstant (A := A) (a i)) (boundedConstant (A := A) (a i)*x v)).mpr
        (hx (.comm i v))
      rw [mk_mul,mk_mul] at h
      exact h
    have hm : Continuous (normInclusion (A := A) U) := map_continuous _
    exact ha.induction_on b (isClosed_eq (continuous_const.mul hm) (hm.mul continuous_const)) he
  let V : Var→C := fun v=>⟨mk U (x v),hc v⟩
  let w : ℕ→Fω := fun j=>π (V (.inl j))
  let W : Term ℕ→C := fun e=>e.localEval cu (fun j=>V (.inl j))
  let y : Term ℕ→L := fun e=>e.localEval u (fun j=>x (.inl j))
  have hy (e : Term ℕ) : mk U (y e)=(W e:N) := by
    dsimp [y,W]
    rw [e.mk_localEval,hu]
    exact (e.map_localEval cu (fun j=>V (.inl j)) (normCentralInclusion U)).symm
  have hW (e : Term ℕ) : π (W e)=e.eval w := by
    dsimp [W]
    rw [e.map_localEval]
    change e.localEval 1 w=e.eval w
    exact e.localEval_one w
  have haux (e : Term ℕ) : π (W e)=π (V (.inr e)) := by
    apply quotient_eq_of_dense_errors U a ha (W e) (V (.inr e)) (y e) (x (.inr e)) (hy e) rfl
    · intro i
      simpa only [testValue,y,Term.localEval_apply] using hx (.left i e)
    · intro i
      simpa only [testValue,y,Term.localEval_apply] using hx (.right i e)
  have hnorm (e : Term ℕ) : ‖e.eval w‖≤‖e.eval d‖ := by
    rw [←hW e,haux e]
    apply (NonUnitalStarAlgHom.norm_apply_le π (V (.inr e))).trans
    change ‖mk U (x (.inr e))‖≤‖e.eval d‖
    rw [norm_mk_eq_limsup]
    apply le_of_forall_pos_le_add
    intro ε hε
    apply limsup_le_of_le (BoundedFamilies.norm_cobounded U (x (.inr e)))
    have ht := (tendsto_order.mp (hx (.norm e))).2 ε hε
    filter_upwards [ht] with k hk
    change max (‖x (.inr e) k‖-‖e.eval d‖) 0<ε at hk
    have := le_max_left (‖x (.inr e) k‖-‖e.eval d‖) 0
    linarith
  have hwI : w 0=algebraMap ℂ Fω Complex.I := by
    have hIq : π (V (.inl 0))=π ((Complex.I:ℂ)•cu) := by
      apply quotient_eq_of_dense_errors U a ha (V (.inl 0)) ((Complex.I:ℂ)•cu)
        (x (.inl 0)) ((Complex.I:ℂ)•u) rfl
        (by rw [mk_smul,hu]; rfl)
      · intro i; exact hx (.imagLeft i)
      · intro i; exact hx (.imagRight i)
    exact hIq.trans ((map_smul π Complex.I cu).trans (Algebra.algebraMap_eq_smul_one Complex.I).symm)
  have hS : Dense (evalRange d : Set D) := hd.mono (by rintro z ⟨j,rfl⟩; exact ⟨.gen j,rfl⟩)
  have hI : algebraMap ℂ D Complex.I∈evalRange d := ⟨.gen 0,hdI⟩
  let f := RationalTerms.lift d w hnorm
  have hfI : f ⟨algebraMap ℂ D Complex.I,hI⟩=algebraMap ℂ Fω Complex.I := by
    exact (liftedValue_eq d w hnorm ⟨algebraMap ℂ D Complex.I,hI⟩ (.gen 0) hdI).trans hwI
  exact ⟨RationalStarExtension.extension (evalRange d) hS f
    (RationalTerms.lift_norm d w hnorm) hI hfI⟩

end NonunitalCentralSaturation

end
end

end OAI
