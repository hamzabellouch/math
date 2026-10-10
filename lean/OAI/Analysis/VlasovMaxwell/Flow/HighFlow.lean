import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.TameDerivative
import OAI.Analysis.VlasovMaxwell.Regularity.SmoothIntegral
import OAI.Analysis.VlasovMaxwell.Regularity.VelocityDerivatives
import OAI.Analysis.VlasovMaxwell.Regularity.CurvatureBounds

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace E]

omit [ProperSpace E] [CompleteSpace E] in
lemma iteratedFDeriv_id_high (n : ℕ) (hn : 1 ≤ n) (x : E) :
    iteratedFDeriv ℝ (n+1) (id : E → E) x=0 := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_id,iteratedFDeriv_const_of_ne (by omega : n≠0),Function.comp_apply,
    Pi.zero_apply,map_zero]

lemma tame_flow_iteratedFDeriv (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V Y : ℝ × E → E), ContDiff ℝ ∞ V → ContDiff ℝ ∞ Y →
      ∀ T ∈ Icc (0:ℝ) 1, ∀ H : ℝ, 0 ≤ H →
      (∀ t ∈ Icc 0 T, ∀ x, Y (t,x)=x+∫ r in 0..t, V (r,Y (r,x))) →
      (∀ t ∈ Icc 0 T, ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z => V (t,z)) (Y (t,x))‖ ≤ A ∧
        ‖iteratedFDeriv ℝ i (fun z => Y (t,z)) x‖ ≤ A) →
      (∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun z => V (t,z)) (Y (t,x))‖ ≤ H) →
      ∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun z => Y (t,z)) x‖ ≤ C*(1+H) := by
  obtain ⟨K,hK,hcomp⟩ := tame_iteratedFDeriv_comp (E:=E) (F:=E) (G:=E) n hn A hA
  refine ⟨K*Real.exp K,by positivity,?_⟩
  intro V Y hV hY T hT H hH heq hlow htop t ht x
  let Z : ℝ × E → E := fun p => V (p.1,Y p)
  have hZ : ContDiff ℝ ∞ Z := hV.comp (contDiff_fst.prodMk hY)
  let f : ℝ → ℝ := fun r => ‖iteratedFDeriv ℝ (n+1) (fun z => Y (r,z)) x‖
  have hf : Continuous f := ((contDiff_iteratedFDeriv_slice hY (n+1)).continuous.comp
    (continuous_id.prodMk continuous_const)).norm
  have hb (r : ℝ) (hr : r ∈ Icc 0 T) : f r ≤ K*(1+H)+K*∫ v in 0..r, f v := by
    have hfun : (fun z => Y (r,z)) = (fun z => z+∫ v in 0..r, Z (v,z)) := funext (heq r hr)
    have hint := (contDiff_spatial_intervalIntegral hZ hr.1).of_le (by exact_mod_cast le_top : (n+1:ℕ) ≤ (∞:ℕ∞ω))
    have hder := fun_iteratedFDeriv_add (contDiff_id : ContDiff ℝ (n+1) (id : E → E)) hint
    have hid := iteratedFDeriv_id_high (E:=E) n hn x
    have hzbound (v : ℝ) (hv : v ∈ Icc 0 r) :
        ‖iteratedFDeriv ℝ (n+1) (fun z => Z (v,z)) x‖ ≤ K*(1+H+f v) := by
      have hvT : v ∈ Icc 0 T := ⟨hv.1,hv.2.trans hr.2⟩
      have hh := hcomp (fun z => V (v,z)) (fun z => Y (v,z))
        (hV.comp (contDiff_const.prodMk contDiff_id)) (hY.comp (contDiff_const.prodMk contDiff_id)) x
        (fun i hi hi' => (hlow v hvT x i hi hi').1)
        (fun i hi hi' => (hlow v hvT x i hi hi').2)
      exact hh.trans (mul_le_mul_of_nonneg_left (by gcongr; exact htop v hvT x) hK)
    have hzi : Continuous (fun v => ‖iteratedFDeriv ℝ (n+1) (fun z => Z (v,z)) x‖) :=
      ((contDiff_iteratedFDeriv_slice hZ (n+1)).continuous.comp
        (continuous_id.prodMk continuous_const)).norm
    have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.1 (hzi.intervalIntegrable 0 r)
      ((continuous_const.mul ((continuous_const.add continuous_const).add hf)).intervalIntegrable 0 r) hzbound
    have hcint : (∫ v in 0..r, K*(1+H+f v))=K*(1+H)*r+K*∫ v in 0..r, f v := by
      simp_rw [mul_add]
      rw [intervalIntegral.integral_add (intervalIntegrable_const) ((hf.intervalIntegrable 0 r).const_mul K),
        intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
      simp only [sub_zero,smul_eq_mul]
      ring
    calc
      f r = ‖iteratedFDeriv ℝ (n+1) (fun z => ∫ v in 0..r, Z (v,z)) x‖ := by
        dsimp [f]
        rw [hfun]
        have hd : iteratedFDeriv ℝ (n+1) (fun z => z+∫ v in 0..r, Z (v,z)) x =
            iteratedFDeriv ℝ (n+1) (id : E → E) x+
              iteratedFDeriv ℝ (n+1) (fun z => ∫ v in 0..r, Z (v,z)) x := congrFun hder x
        rw [hd,hid,zero_add]
      _  ≤  ∫ v in 0..r, ‖iteratedFDeriv ℝ (n+1) (fun z => Z (v,z)) x‖ :=
        norm_iteratedFDeriv_intervalIntegral_le hZ (n+1) hr.1 x
      _  ≤  K*(1+H)*r+K*∫ v in 0..r, f v := hi.trans_eq hcint
      _  ≤  K*(1+H)+K*∫ v in 0..r, f v := by
        have hh := mul_le_mul_of_nonneg_left (hr.2.trans hT.2) (mul_nonneg hK (by linarith : 0≤1+H))
        nlinarith only [hh]
  have hg := integral_gronwall_bound hf (mul_nonneg hK (by linarith)) hK
    (fun r _ => norm_nonneg _) hb t ht
  exact hg.trans (by
    calc
      K*(1+H)*Real.exp (K*t)  ≤  K*(1+H)*Real.exp K := by
        gcongr
        nlinarith [ht.2.trans hT.2]
      _ = K*Real.exp K*(1+H) := by ring)

end

def SpatialJetBound (n : ℕ) (T A : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x, ∀ i : ℕ, i ≤ n →
    ‖iteratedFDeriv ℝ i (fun y => E (t,y)) x‖ ≤ A ∧
    ‖iteratedFDeriv ℝ i (fun y => B (t,y)) x‖ ≤ A

private def lorentzNonlinearity (w : Vec × (Vec × Vec)) : Phase :=
  (w.1,w.2.1+cross w.1 w.2.2)

private lemma lorentzNonlinearity_smooth : ContDiff ℝ ∞ lorentzNonlinearity :=
  contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).add
    (contDiff_cross.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))))

private def lorentzArgument (E B : Vec → Vec) (z : Phase) : Vec × (Vec × Vec) :=
  (velocity z.2,(E z.1,B z.1))

private lemma lorentzArgument_smooth {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (lorentzArgument E B) :=
  (contDiff_velocity.comp contDiff_snd).prodMk ((hE.comp contDiff_fst).prodMk (hB.comp contDiff_fst))

private lemma lorentzArgument_derivative_le {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (i : ℕ) (z : Phase) {C : ℝ}
    (hv : ‖iteratedFDeriv ℝ i velocity z.2‖ ≤ C)
    (he : ‖iteratedFDeriv ℝ i E z.1‖ ≤ C) (hb : ‖iteratedFDeriv ℝ i B z.1‖ ≤ C) :
    ‖iteratedFDeriv ℝ i (lorentzArgument E B) z‖ ≤ C := by
  apply norm_iteratedFDeriv_pair_le (contDiff_velocity.comp contDiff_snd)
    ((hE.comp contDiff_fst).prodMk (hB.comp contDiff_fst))
  · exact (norm_iteratedFDeriv_precomp_contraction velocity contDiff_velocity
      (ContinuousLinearMap.snd ℝ Vec Vec) (ContinuousLinearMap.norm_snd_le ℝ Vec Vec) i z).trans hv
  · apply norm_iteratedFDeriv_pair_le (hE.comp contDiff_fst) (hB.comp contDiff_fst)
    · exact (norm_iteratedFDeriv_precomp_contraction E hE
        (ContinuousLinearMap.fst ℝ Vec Vec) (ContinuousLinearMap.norm_fst_le ℝ Vec Vec) i z).trans he
    · exact (norm_iteratedFDeriv_precomp_contraction B hB
        (ContinuousLinearMap.fst ℝ Vec Vec) (ContinuousLinearMap.norm_fst_le ℝ Vec Vec) i z).trans hb

private lemma lorentzArgument_mem {E B : Vec → Vec} {A : ℝ} (hA : 1 ≤ A)
    (he : ∀ x, ‖E x‖ ≤ A) (hb : ∀ x, ‖B x‖ ≤ A) (z : Phase) :
    lorentzArgument E B z∈closedBall (0:Vec × (Vec × Vec)) A := by
  rw [mem_closedBall_zero_iff]
  exact max_le ((norm_velocity_lt_one z.2).le.trans hA) (max_le (he z.1) (hb z.1))

lemma lorentzField_derivatives_bound (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ T, SpatialJetBound n T A E B → ∀ t∈Icc 0 T, ∀ z, ∀ i : ℕ, i ≤ n →
        ‖iteratedFDeriv ℝ i (fun w => lorentzField E B (t,w)) z‖ ≤ C := by
  have hv (i : Fin (n+1)) := velocity_derivatives_bounded i
  choose V hV hbV using hv
  let D := A+∑ i, V i
  have hAD : A ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hV i))
  have hVD (i : Fin (n+1)) : V i ≤ D :=
    (Finset.single_le_sum (fun j _ => hV j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hA))
  obtain ⟨C,hC,hcomp⟩ := bounded_derivatives_comp_on_compact (U:=Phase) lorentzNonlinearity_smooth
    (isCompact_closedBall (0:Vec × (Vec × Vec)) A) n D (hA.trans hAD)
  refine ⟨C,hC,?_⟩
  intro E B hE hB T hbound t ht z i hi
  have he : ContDiff ℝ ∞ (fun x => E (t,x)) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hb : ContDiff ℝ ∞ (fun x => B (t,x)) := hB.comp (contDiff_const.prodMk contDiff_id)
  apply hcomp (lorentzArgument (fun x => E (t,x)) (fun x => B (t,x))) (lorentzArgument_smooth he hb) z
  · apply lorentzArgument_mem hA
    · intro x; simpa only [norm_iteratedFDeriv_zero] using (hbound t ht x 0 (Nat.zero_le _)).1
    · intro x; simpa only [norm_iteratedFDeriv_zero] using (hbound t ht x 0 (Nat.zero_le _)).2
  · intro j hj hj'
    exact lorentzArgument_derivative_le he hb j z ((hbV ⟨j,by omega⟩ z.2).trans (hVD _))
      ((hbound t ht z.1 j hj').1.trans hAD) ((hbound t ht z.1 j hj').2.trans hAD)
  · exact hi

lemma lorentzField_derivative_tame (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ T, SpatialJetBound n T A E B → ∀ H : ℝ, 0 ≤ H →
      (∀ t∈Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun y => E (t,y)) x‖ ≤ H ∧
        ‖iteratedFDeriv ℝ (n+1) (fun y => B (t,y)) x‖ ≤ H) →
      ∀ t∈Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ (n+1) (fun w => lorentzField E B (t,w)) z‖ ≤ C*(1+H) := by
  have hv (i : Fin (n+2)) := velocity_derivatives_bounded i
  choose V hV hbV using hv
  let D := A+∑ i, V i
  have hAD : A ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hV i))
  have hD : 0 ≤ D := (zero_le_one.trans hA).trans hAD
  have hVD (i : Fin (n+2)) : V i ≤ D :=
    (Finset.single_le_sum (fun j _ => hV j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hA))
  obtain ⟨C,hC,hcomp⟩ := tame_comp_on_compact (U:=Phase) lorentzNonlinearity_smooth
    (isCompact_closedBall (0:Vec × (Vec × Vec)) A) n hn D (hA.trans hAD)
  refine ⟨C*(1+D),by positivity,?_⟩
  intro E B hE hB T hbound H hH htop t ht z
  have he : ContDiff ℝ ∞ (fun x => E (t,x)) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hb : ContDiff ℝ ∞ (fun x => B (t,x)) := hB.comp (contDiff_const.prodMk contDiff_id)
  have harg := lorentzArgument_smooth he hb
  have hh := hcomp (lorentzArgument (fun x => E (t,x)) (fun x => B (t,x))) harg z
    (lorentzArgument_mem hA
      (fun x => by simpa only [norm_iteratedFDeriv_zero] using (hbound t ht x 0 (Nat.zero_le _)).1)
      (fun x => by simpa only [norm_iteratedFDeriv_zero] using (hbound t ht x 0 (Nat.zero_le _)).2) z)
    (fun j hj hj' => lorentzArgument_derivative_le he hb j z ((hbV ⟨j,by omega⟩ z.2).trans (hVD _))
      ((hbound t ht z.1 j hj').1.trans hAD) ((hbound t ht z.1 j hj').2.trans hAD))
  have hargtop := lorentzArgument_derivative_le he hb (n+1) z
    (((hbV ⟨n+1,by omega⟩ z.2).trans (hVD _)).trans (le_add_of_nonneg_right hH))
    ((htop t ht z.1).1.trans (le_add_of_nonneg_left hD))
    ((htop t ht z.1).2.trans (le_add_of_nonneg_left hD))
  apply hh.trans
  have hi := mul_le_mul_of_nonneg_left (add_le_add_left hargtop 1) hC
  nlinarith [mul_nonneg hD hH,mul_nonneg hC (mul_nonneg hD hH)]

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace E]

lemma flow_first_derivative_bound {V Y : ℝ × E → E}
    (hV : ContDiff ℝ ∞ V) (hY : ContDiff ℝ ∞ Y) {T : ℝ} (hT : T∈Icc (0:ℝ) 1)
    {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ t∈Icc 0 T, ∀ x, Y (t,x)=x+∫ r in 0..t, V (r,Y (r,x)))
    (hbound : ∀ t∈Icc 0 T, ∀ x, ‖fderiv ℝ (fun z => V (t,z)) (Y (t,x))‖ ≤ A)
    {t : ℝ} (ht : t∈Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun z => Y (t,z)) x‖ ≤ Real.exp A := by
  let Z : ℝ × E → E := fun p => V (p.1,Y p)
  have hZ : ContDiff ℝ ∞ Z := hV.comp (contDiff_fst.prodMk hY)
  let f : ℝ → ℝ := fun r => ‖iteratedFDeriv ℝ 1 (fun z => Y (r,z)) x‖
  have hf : Continuous f := ((contDiff_iteratedFDeriv_slice hY 1).continuous.comp
    (continuous_id.prodMk continuous_const)).norm
  have hb (r : ℝ) (hr : r∈Icc 0 T) : f r ≤ 1+A*∫ v in 0..r, f v := by
    have hfun : (fun z => Y (r,z))=(fun z => z+∫ v in 0..r, Z (v,z)) := funext (heq r hr)
    have hint := (contDiff_spatial_intervalIntegral hZ hr.1).of_le (by simp : (1:ℕ∞ω) ≤ ∞)
    have hder : iteratedFDeriv ℝ 1 (fun z => z+∫ v in 0..r, Z (v,z)) x =
        iteratedFDeriv ℝ 1 (id : E → E) x+iteratedFDeriv ℝ 1 (fun z => ∫ v in 0..r, Z (v,z)) x :=
      congrFun (fun_iteratedFDeriv_add (contDiff_id : ContDiff ℝ 1 (id : E → E)) hint) x
    have hzi : Continuous (fun v => ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖) :=
      ((contDiff_iteratedFDeriv_slice hZ 1).continuous.comp (continuous_id.prodMk continuous_const)).norm
    have hg (v : ℝ) (hv : v∈Icc 0 r) : ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖ ≤ A*f v := by
      dsimp [Z,f]
      simp only [norm_iteratedFDeriv_one]
      have he : (fun z => V (v,Y (v,z)))=(fun z => V (v,z)) ∘ (fun z => Y (v,z)) := rfl
      have hvD : Differentiable ℝ (fun z => V (v,z)) :=
        (hV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
      have hyD : Differentiable ℝ (fun z => Y (v,z)) :=
        (hY.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
      rw [he,fderiv_comp x (hvD _) (hyD _)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hbound v ⟨hv.1,hv.2.trans hr.2⟩ x) (norm_nonneg _))
    have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.1 (hzi.intervalIntegrable 0 r)
      ((continuous_const.mul hf).intervalIntegrable 0 r) hg
    calc
      f r = ‖iteratedFDeriv ℝ 1 (fun z => z+∫ v in 0..r, Z (v,z)) x‖ := by dsimp [f]; rw [hfun]
      _ ≤ ‖iteratedFDeriv ℝ 1 (id : E → E) x‖+
          ‖iteratedFDeriv ℝ 1 (fun z => ∫ v in 0..r, Z (v,z)) x‖ := by rw [hder]; exact norm_add_le _ _
      _ ≤ 1+∫ v in 0..r, ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖ := by
        apply add_le_add
        · simp only [norm_iteratedFDeriv_one,fderiv_id]; exact ContinuousLinearMap.norm_id_le
        · exact norm_iteratedFDeriv_intervalIntegral_le hZ 1 hr.1 x
      _ ≤ 1+A*∫ v in 0..r, f v := by
        have hi' : (∫ v in 0..r, ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖) ≤ A*∫ v in 0..r, f v := by
          simpa only [Pi.mul_apply,intervalIntegral.integral_const_mul] using hi
        exact add_le_add le_rfl hi'
  have hh := integral_gronwall_bound hf zero_le_one hA (fun r _ => norm_nonneg _) hb t ht
  apply hh.trans
  simp only [one_mul]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (ht.2.trans hT.2) hA).trans_eq (mul_one _)

lemma flow_derivatives_bound (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V Y : ℝ × E → E), ContDiff ℝ ∞ V → ContDiff ℝ ∞ Y →
      ∀ T∈Icc (0:ℝ) 1,
      (∀ t∈Icc 0 T, ∀ x, Y (t,x)=x+∫ r in 0..t, V (r,Y (r,x))) →
      (∀ t∈Icc 0 T, ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z => V (t,z)) (Y (t,x))‖ ≤ A) →
      ∀ t∈Icc 0 T, ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z => Y (t,z)) x‖ ≤ C := by
  induction n with
  | zero => exact ⟨0,le_rfl,fun V Y hV hY T hT heq hb t ht x i hi hin => by omega⟩
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      refine ⟨Real.exp A,(Real.exp_pos _).le,?_⟩
      intro V Y hV hY T hT heq hb t ht x i hi hi'
      have he : i=1 := by omega
      subst i
      exact flow_first_derivative_bound hV hY hT (zero_le_one.trans hA) heq
        (fun r hr z => by simpa only [norm_iteratedFDeriv_one] using hb r hr z 1 le_rfl le_rfl) ht x
    · obtain ⟨D,hD,hd⟩ := ih
      obtain ⟨C,hC,hhigh⟩ := tame_flow_iteratedFDeriv (E:=E) n (by omega) (max A D) (hA.trans (le_max_left _ _))
      refine ⟨max D (C*(1+A)),le_max_of_le_left hD,?_⟩
      intro V Y hV hY T hT heq hb t ht x i hi hi'
      have hy := hd V Y hV hY T hT heq (fun r hr z j hj hj' => hb r hr z j hj (by omega))
      by_cases hin : i ≤ n
      · exact (hy t ht x i hi hin).trans (le_max_left _ _)
      · have he : i=n+1 := by omega
        subst i
        exact (hhigh V Y hV hY T hT A (zero_le_one.trans hA) heq
          (fun r hr z j hj hj' => ⟨(hb r hr z j hj (by omega)).trans (le_max_left _ _),
            (hy r hr z j hj hj').trans (le_max_right _ _)⟩)
          (fun r hr z => hb r hr z (n+1) (by omega) le_rfl) t ht x).trans (le_max_right _ _)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothLorentzFlow.reversePath_smooth {E B : Field} (F : SmoothLorentzFlow E B) (t : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => F.reversePath t p.2 p.1) := by
  exact F.smooth_forward.comp ((contDiff_const.sub contDiff_fst).prodMk
    (F.smooth_backward.comp (contDiff_const.prodMk contDiff_snd)))

lemma SmoothLorentzFlow.reversePath_integral {E B : Field} (F : SmoothLorentzFlow E B)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (t u : ℝ) (z : Phase) :
    F.reversePath t z u=z+∫ r in 0..u, -lorentzField E B (t-r,F.reversePath t z r) := by
  have hc : Continuous (fun r => -lorentzField E B (t-r,F.reversePath t z r)) :=
    ((contDiff_lorentzField hE hB).continuous.comp ((continuous_const.sub continuous_id).prodMk
      ((F.reversePath_smooth t).continuous.comp (continuous_id.prodMk continuous_const)))).neg
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => F.reversePath_deriv t r z)
    (hc.intervalIntegrable 0 u)
  rw [F.reversePath_zero] at hh
  rw [hh]
  abel

lemma SmoothLorentzFlow.reversePath_derivatives_bound (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ (F : SmoothLorentzFlow E B) (T : ℝ), T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
      ∀ t∈Icc 0 T, ∀ u∈Icc 0 t, ∀ z, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun w => F.reversePath t w u) z‖ ≤ C := by
  obtain ⟨L,hL,hLor⟩ := lorentzField_derivatives_bound n A hA
  obtain ⟨C,hC,hflow⟩ := flow_derivatives_bound (E:=Phase) n (max 1 L) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro E B hE hB F T hT hbound t ht u hu z i hi hi'
  let V : ℝ × Phase → Phase := fun p => -lorentzField E B (t-p.1,p.2)
  let Y : ℝ × Phase → Phase := fun p => F.reversePath t p.2 p.1
  have hV : ContDiff ℝ ∞ V := ((contDiff_lorentzField hE hB).comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)).neg
  have hY : ContDiff ℝ ∞ Y := F.reversePath_smooth t
  apply hflow V Y hV hY t ⟨ht.1,ht.2.trans hT.2⟩
    (fun r hr x => F.reversePath_integral hE hB t r x) ?_ u hu z i hi hi'
  intro r hr x j hj hj'
  dsimp only [V]
  rw [show (fun z => -lorentzField E B (t-r,z)) = -(fun z => lorentzField E B (t-r,z)) from rfl,
      iteratedFDeriv_neg_apply,norm_neg]
  exact (hLor E B hE hB T hbound (t-r) ⟨by linarith [hr.2],by linarith [hr.1,ht.2]⟩ _ j hj').trans
    (le_max_right _ _)

lemma SmoothLorentzFlow.backward_derivative_tame (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ (F : SmoothLorentzFlow E B) (T : ℝ), T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
      ∀ H : ℝ, 0 ≤ H →
      (∀ t∈Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun y => E (t,y)) x‖ ≤ H ∧
        ‖iteratedFDeriv ℝ (n+1) (fun y => B (t,y)) x‖ ≤ H) →
      ∀ t∈Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ (n+1) (fun w => F.backward (t,w)) z‖ ≤ C*(1+H) := by
  obtain ⟨L,hL,hLor⟩ := lorentzField_derivatives_bound n A hA
  obtain ⟨D,hD,hlow⟩ := SmoothLorentzFlow.reversePath_derivatives_bound n A hA
  obtain ⟨K,hK,hhigh⟩ := lorentzField_derivative_tame n hn A hA
  obtain ⟨C,hC,hflow⟩ := tame_flow_iteratedFDeriv (E:=Phase) n hn (1+L+D) (by linarith)
  refine ⟨C*(1+K),by positivity,?_⟩
  intro E B hE hB F T hT hbound H hH htop t ht z
  let V : ℝ × Phase → Phase := fun p => -lorentzField E B (t-p.1,p.2)
  let Y : ℝ × Phase → Phase := fun p => F.reversePath t p.2 p.1
  have hV : ContDiff ℝ ∞ V := ((contDiff_lorentzField hE hB).comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)).neg
  have hY : ContDiff ℝ ∞ Y := F.reversePath_smooth t
  have hh := hflow V Y hV hY t ⟨ht.1,ht.2.trans hT.2⟩ (K*(1+H)) (by positivity)
    (fun r hr x => F.reversePath_integral hE hB t r x)
    (by
      intro r hr x j hj hj'
      refine ⟨?_,?_⟩
      · dsimp only [V]
        rw [show (fun z => -lorentzField E B (t-r,z)) = -(fun z => lorentzField E B (t-r,z)) from rfl,
      iteratedFDeriv_neg_apply,norm_neg]
        exact (hLor E B hE hB T hbound (t-r) ⟨by linarith [hr.2],by linarith [hr.1,ht.2]⟩ _ j hj').trans (by linarith)
      · exact (hlow E B hE hB F T hT hbound t ht r hr x j hj hj').trans (by linarith))
    (by
      intro r hr x
      dsimp only [V]
      rw [show (fun z => -lorentzField E B (t-r,z)) = -(fun z => lorentzField E B (t-r,z)) from rfl,
      iteratedFDeriv_neg_apply,norm_neg]
      exact hhigh E B hE hB T hbound H hH htop (t-r) ⟨by linarith [hr.2],by linarith [hr.1,ht.2]⟩ _)
    t ⟨ht.1,le_rfl⟩ z
  have hrep : (fun w => Y (t,w))=(fun w => F.backward (t,w)) := by funext w; exact F.reversePath_end t w
  rw [hrep] at hh
  exact hh.trans (by nlinarith [mul_nonneg hC hH])

end RVM

end

end OAI
