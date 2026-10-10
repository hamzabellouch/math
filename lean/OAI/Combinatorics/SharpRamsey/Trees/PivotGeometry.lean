import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.ProducedSupportLoss

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation GeometricCover
open scoped Classical BigOperators
noncomputable section

lemma description_ratio {w Q A B X T b : ℝ} (hT : 0<T) (hX : 0≤X)
    (hAB : Q*exp (-b)≤A*B) (hA : A≤2*X) (hB : B≤2*T)
    (hB0 : 0≤B) (hW : w≤100000*Q/T) :
    w≤exp (b+log 1000000)*X := by
  have hQ : Q≤A*B*exp b := by
    have hh := mul_le_mul_of_nonneg_right hAB (exp_pos b).le
    have he : exp (-b)*exp b=1 := by rw [←exp_add]; simp
    simpa only [mul_assoc,he,mul_one] using hh
  have hprod : A*B≤(2*X)*(2*T) := mul_le_mul hA hB hB0 (by positivity)
  calc
    w ≤ 100000*Q/T := hW
    _ ≤ 100000*(A*B*exp b)/T := by gcongr
    _ ≤ 100000*((2*X)*(2*T)*exp b)/T := by gcongr
    _ = 400000*exp b*X := by field_simp; ring
    _ ≤ 1000000*exp b*X := by gcongr; norm_num
    _ = _ := by rw [exp_add,exp_log (by norm_num : (0:ℝ)<1000000)]; ring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incidence_mono {A S : Finset (Projectivization K V)}
    {B T : Finset (Projectivization K (Module.Dual K V))} (hS : S⊆A) (hT : T⊆B) :
    incidenceCount S T≤ incidenceCount A B := by
  apply (sum_le_sum (fun y (_ : y∈T) => card_le_card (filter_subset_filter _ hS))).trans
  exact sum_le_sum_of_subset_of_nonneg hT (by intros; exact Nat.zero_le _)

theorem trimmed_inputs (A U : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V))) (q Q τ b : ℝ)
    (hq : 0<q) (hτ : 0≤τ) (htrimA : (A.card:ℝ)≤2*(A∩U).card)
    (htrimB : (B.card:ℝ)≤2*(B∩UT).card)
    (hprod : Q*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/q) :
    Q*exp (-(b+log 4))≤((A∩U).card:ℝ)*(B∩UT).card ∧
    (incidenceCount (A∩U) (B∩UT):ℝ)≤4*τ*((A∩U).card:ℝ)*(B∩UT).card/q := by
  have hp : (A.card:ℝ)*B.card≤4*((A∩U).card:ℝ)*(B∩UT).card := by
    have hh := mul_le_mul htrimA htrimB (Nat.cast_nonneg _) (show 0≤2*((A∩U).card:ℝ) by positivity)
    nlinarith only [hh]
  constructor
  · have he : exp (-(b+log 4))=exp (-b)/4 := by
      rw [neg_add,exp_add,exp_neg (log 4),exp_log (by norm_num : (0:ℝ)<4)]; ring
    rw [he]
    linarith
  · have hm : (incidenceCount (A∩U) (B∩UT):ℝ)≤ incidenceCount A B := by
      exact_mod_cast incidence_mono (inter_subset_left) (inter_subset_left)
    apply hm.trans (hsp.trans _)
    have hh := mul_le_mul_of_nonneg_left hp hτ
    convert div_le_div_of_nonneg_right hh hq.le using 1 <;> ring

theorem first_source (A U : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V))) (q τ b : ℝ) (r : ℕ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hq : 0<q) (hτ : 0≤τ)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (hprod : q^r*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/q)
    (F : Finset (Finset (Projectivization K V)))
    (hF : ∀ W∈F,W⊆U ∧ (W.card:ℝ)≤100000*q^r/(B∩UT).card)
    (hc : ∀ S T,S⊆U → S.card=(A∩U).card → T⊆UT → T.card=(B∩UT).card →
      (incidenceCount S T:ℝ)≤4*τ*((A∩U).card:ℝ)*(B∩UT).card/q →
      ∃ W∈F,(99/100:ℝ)*(A∩U).card≤(S∩W).card) :
    ∃ W∈F,W⊆U ∧ ((A∩U)∩W).Nonempty ∧
      (A.card:ℝ)≤2*((A∩U)∩W).card ∧
      (W.card:ℝ)≤exp (b+log 1000000)*((A∩U)∩W).card := by
  have hA' : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hB' : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hcutA : (A.card:ℝ)≤2*(A∩U).card := by linarith
  have hcutB : (B.card:ℝ)≤2*(B∩UT).card := by linarith
  have hcutsp := (trimmed_inputs A U B UT q (q^r) τ b hq hτ hcutA hcutB hprod hsp).2
  obtain ⟨W,hW,hcapture⟩ := hc (A∩U) (B∩UT) inter_subset_right rfl inter_subset_right rfl hcutsp
  have hcap : (A.card:ℝ)≤2*((A∩U)∩W).card := by linarith
  have hx : (0:ℝ)<((A∩U)∩W).card := by linarith
  have ht : (0:ℝ)<(B∩UT).card := by linarith
  refine ⟨W,hW,(hF W hW).1,card_pos.mp (by exact_mod_cast hx),hcap,?_⟩
  exact description_ratio ht hx.le hprod hcap hcutB (Nat.cast_nonneg _) (hF W hW).2

theorem second_source {Ω : Type*} (B T W : Finset Ω)
    (hB : B.Nonempty) (htrim : (9/10:ℝ)*B.card≤T.card)
    (hcap : (99:ℝ)*T.card≤100*(T∩W).card) :
    (T∩W).Nonempty ∧ (B.card:ℝ)≤2*(T∩W).card := by
  have hb : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hc : (B.card:ℝ)≤2*(T∩W).card := by linarith
  refine ⟨card_pos.mp ?_,hc⟩
  exact_mod_cast (by linarith : (0:ℝ)<(T∩W).card)

end
end SharpLogRamsey.PivotGeometry

end

end OAI
