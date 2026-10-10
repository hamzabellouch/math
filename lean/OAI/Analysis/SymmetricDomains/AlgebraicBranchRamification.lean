import Mathlib
import OAI.Analysis.SymmetricDomains.RealParameterPolarRemoval
import OAI.Analysis.SymmetricDomains.PolynomialRamifiedAnalyticRoot
import OAI.Analysis.SymmetricDomains.MeromorphicPolynomialRoot

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Filter Set Complex UpperHalfPlane Function
open scoped Topology

theorem continuous_polynomial_roots_eq {d : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : X → (Fin d → ℂ))
    (hA : Continuous A)
    (hlead : ∀ x, MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x, (P.map (MvPolynomial.eval (A x))).Separable)
    (g h : X → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hgr : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x)) (g x) P = 0)
    (hhr : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x)) (h x) P = 0)
    (x₀ : X) (h₀ : g x₀ = h x₀) : g = h := by
  let R := {r : X × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0}
  let G : X → R := fun x => ⟨(x,g x),hgr x⟩
  let H : X → R := fun x => ⟨(x,h x),hhr x⟩
  have he : G = H := (polynomial_root_covering P A hA hlead hsep).eq_of_comp_eq
    ((continuous_id.prodMk hg).subtype_mk _) ((continuous_id.prodMk hh).subtype_mk _)
    rfl x₀ (Subtype.ext (Prod.ext rfl h₀))
  exact funext fun x => congrArg (fun r : R => r.val.2) (congrFun he x)

noncomputable def unitImaginaryHalfPlane : ℍ := ⟨Complex.I,by simp⟩

theorem halfPlaneQ_unitImaginary (h : ℝ) (hh : 0 < h) :
    (halfPlaneQ h hh unitImaginaryHalfPlane).val =
      (Real.exp (-2 * Real.pi / h) : ℂ) := by
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * Complex.I / (h : ℂ)) = _
  rw [show 2 * (Real.pi : ℂ) * Complex.I * Complex.I / (h : ℂ) =
    ((-2 * Real.pi / h : ℝ) : ℂ) from by
      push_cast
      rw [mul_assoc (2 * (Real.pi : ℂ)),Complex.I_mul_I]
      ring]
  exact Complex.ofReal_exp _ |>.symm

theorem halfPlaneQ_unitImaginary_real_bounds (h : ℝ) (hh : 0 < h) :
    0 < Real.exp (-2 * Real.pi / h) ∧ Real.exp (-2 * Real.pi / h) < 1 := by
  refine ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr ?_⟩
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hh

end

open Filter Set Metric Complex
open scoped Topology

noncomputable def realParameter {n : ℕ} (s : Fin n → ℝ) : Fin n → ℂ := fun i => (s i : ℂ)

theorem realParameter_zero {n : ℕ} : realParameter (0 : Fin n → ℝ) = 0 := by
  ext i
  exact Complex.ofReal_zero

theorem continuous_realParameter (n : ℕ) : Continuous (realParameter (n := n)) :=
  continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))

theorem norm_realParameter {n : ℕ} (s : Fin n → ℝ) : ‖realParameter s‖ = ‖s‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realParameter,Complex.norm_real] using norm_le_pi_norm s i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realParameter,Complex.norm_real] using norm_le_pi_norm (realParameter s) i

theorem realParameter_mem_ball {n : ℕ} {s : Fin n → ℝ} {r : ℝ} (hs : s ∈ ball 0 r) :
    realParameter s ∈ ball 0 r := by
  simpa only [mem_ball,dist_zero_right,norm_realParameter] using hs

theorem algebraic_real_parameter_removal {n d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (A : (Fin n → ℂ) × ℂ → (Fin d → ℂ))
    {r R S : ℝ} (hr : 0 < r) (hR : 0 < R) (hRS : R < S)
    (hA : AnalyticOnNhd ℂ A (ball 0 r ×ˢ ball 0 S))
    (f : (Fin n → ℂ) × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 r ×ˢ (ball 0 S \ {0})))
    (hroot : ∀ p ∈ ball 0 r ×ˢ (ball 0 S \ {0}),
      Polynomial.eval₂ (MvPolynomial.eval (A p)) (f p) P = 0)
    (hlead : ∀ p ∈ ball 0 r ×ˢ (ball 0 S \ {0}),
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0)
    {B ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s : Fin n → ℝ, ‖s‖ < r → ∀ t : ℝ, 0 < t → t < ε →
      ‖f (realParameter s,t)‖ ≤ B) :
    ∃ g : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) ∧
      EqOn g f (ball 0 r ×ˢ (ball 0 R \ {0})) := by
  apply real_parameter_polar_removal hr hR hRS f hf _ hε hb
  intro s hs
  have hsc : realParameter s ∈ ball 0 r := realParameter_mem_ball (by simpa using hs)
  have hAs : AnalyticAt ℂ (fun u => A (realParameter s,u)) 0 :=
    (hA (realParameter s,0) ⟨hsc,mem_ball_self (hR.trans hRS)⟩).comp
      (analyticAt_const.prod analyticAt_id)
  have heu : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ ball 0 S \ {0} := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hR.trans hRS)))] with u hu huS
    exact ⟨huS,hu⟩
  apply meromorphicAt_polynomial_root P (fun u => A (realParameter s,u)) hAs (fun u => f (realParameter s,u))
  · exact heu.mono fun u hu => (hf (realParameter s,u) ⟨hsc,hu⟩).comp
      (analyticAt_const.prod analyticAt_id)
  · exact heu.mono fun u hu => hroot (realParameter s,u) ⟨hsc,hu⟩
  · intro hz
    obtain ⟨u,hu,huz⟩ := (heu.and (hz.filter_mono nhdsWithin_le_nhds)).exists
    exact hlead (realParameter s,u) ⟨hsc,hu⟩ huz

theorem ramified_real_branch_match {n d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (A : (Fin n → ℂ) × ℂ → (Fin d → ℂ))
    {r : ℝ} (hA : ContinuousOn A (ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}))
    (hlead : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0)
    (hsep : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      (P.map (MvPolynomial.eval (A p))).Separable)
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hb : ContinuousOn b (ball 0 r ×ˢ Ioo 0 1))
    (hbr : ∀ (p : (Fin n → ℝ) × ℝ), p ∈ ball 0 r ×ˢ Ioo 0 1 →
      Polynomial.eval₂ (MvPolynomial.eval (A (realParameter p.1,p.2))) (b p) P = 0)
    (l : ℕ) (hl : 0 < l) (G : (Fin n → ℂ) × ℂ → ℂ)
    (hG : ContinuousOn G (ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}))
    (hGr : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      Polynomial.eval₂ (MvPolynomial.eval (A (p.1,p.2^l))) (G p) P = 0)
    (s₀ : Fin n → ℝ) (hs₀ : s₀ ∈ ball 0 r) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (h₀ : G (realParameter s₀,t₀) = b (s₀,t₀^l)) :
    ∀ s ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) 1,
      G (realParameter s,t) = b (s,t^l) := by
  let : ContractibleSpace (ball (0 : Fin n → ℝ) r) :=
    (convex_ball (0 : Fin n → ℝ) r).contractibleSpace ⟨s₀,hs₀⟩
  let : ContractibleSpace (Ioo (0 : ℝ) 1) := (convex_Ioo (𝕜 := ℝ) 0 1).contractibleSpace ⟨t₀,ht₀⟩
  let X := (ball (0 : Fin n → ℝ) r) × (Ioo (0 : ℝ) 1)
  let ι : X → (Fin n → ℂ) × ℂ := fun x => (realParameter x.1.val,x.2.val)
  let κ : X → (Fin n → ℂ) × ℂ := fun x => (realParameter x.1.val,(x.2.val : ℂ)^l)
  let β : X → (Fin n → ℝ) × ℝ := fun x => (x.1.val,x.2.val^l)
  have hιc : Continuous ι :=
    ((continuous_realParameter n).comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd))
  have hκc : Continuous κ := hιc.fst.prodMk (hιc.snd.pow l)
  have hβc : Continuous β := (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_subtype_val.comp continuous_snd).pow l)
  have hι (x : X) : ι x ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} := by
    refine ⟨realParameter_mem_ball x.1.property,?_,?_⟩
    · change (x.2.val : ℂ) ≠ 0
      exact_mod_cast x.2.property.1.ne'
    · simpa only [ι,Complex.norm_real,Real.norm_eq_abs,abs_of_pos x.2.property.1] using x.2.property.2
  have hκ (x : X) : κ x ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} := by
    refine ⟨(hι x).1,pow_ne_zero l (hι x).2.1,?_⟩
    change ‖(x.2.val : ℂ)^l‖ < 1
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hι x).2.2 hl.ne'
  have hβ (x : X) : β x ∈ ball 0 r ×ˢ Ioo 0 1 :=
    ⟨x.1.property,pow_pos x.2.property.1 l,pow_lt_one₀ x.2.property.1.le x.2.property.2 hl.ne'⟩
  have hgcont : Continuous (G ∘ ι) := hG.comp_continuous hιc hι
  have hbcont : Continuous (b ∘ β) := hb.comp_continuous hβc hβ
  have he := continuous_polynomial_roots_eq P (A ∘ κ) (hA.comp_continuous hκc hκ)
    (fun x => hlead (κ x) (hκ x)) (fun x => hsep (κ x) (hκ x))
    (G ∘ ι) (b ∘ β) hgcont hbcont
    (fun x => hGr (ι x) (hι x))
    (fun x => by simpa only [Function.comp_apply,κ,β,Complex.ofReal_pow] using hbr (β x) (hβ x))
    (⟨s₀,hs₀⟩,⟨t₀,ht₀⟩) h₀
  intro s hs t ht
  exact congrFun he (⟨s,hs⟩,⟨t,ht⟩)

theorem bounded_algebraic_branch_ramification {n d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (A : (Fin n → ℂ) × ℂ → (Fin d → ℂ))
    {r : ℝ} (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball 0 r ×ˢ ball 0 1))
    (hlead : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0)
    (hsep : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      (P.map (MvPolynomial.eval (A p))).Separable)
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hb : ContinuousOn b (ball 0 r ×ˢ Ioo 0 1))
    (hbr : ∀ (p : (Fin n → ℝ) × ℝ), p ∈ ball 0 r ×ˢ Ioo 0 1 →
      Polynomial.eval₂ (MvPolynomial.eval (A (realParameter p.1,p.2))) (b p) P = 0)
    {B : ℝ} (hbound : ∀ p ∈ ball 0 r ×ˢ Ioo 0 1, ‖b p‖ ≤ B) :
    ∃ l : ℕ, 0 < l ∧ ∃ F : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball 0 r ×ˢ ball 0 (1/2)) ∧
      ∀ s ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) (1/2),
        F (realParameter s,t) = b (s,t^l) := by
  let : ContractibleSpace (ball (0 : Fin n → ℂ) r) :=
    (convex_ball (0 : Fin n → ℂ) r).contractibleSpace ⟨0,mem_ball_self hr⟩
  let : LocallyPathConnectedSpace (ball (0 : Fin n → ℂ) r) :=
    isOpen_ball.locallyPathConnectedSpace
  let t₁ : ℝ := Real.exp (-2 * Real.pi / 1)
  have ht₁ : t₁ ∈ Ioo (0 : ℝ) 1 := halfPlaneQ_unitImaginary_real_bounds 1 one_pos
  have hA' : AnalyticOnNhd ℂ A (ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}) :=
    hA.mono (fun p hp => ⟨hp.1,by simpa only [mem_ball,dist_zero_right] using hp.2.2⟩)
  have hroot₀ : Polynomial.eval₂
      (MvPolynomial.eval (A (0,(halfPlaneQ 1 one_pos unitImaginaryHalfPlane).val))) (b (0,t₁)) P = 0 := by
    rw [halfPlaneQ_unitImaginary]
    simpa only [t₁,realParameter_zero] using
      hbr (0,t₁) ⟨mem_ball_self hr,ht₁⟩
  obtain ⟨l,hl,G,hGa,hGr,hG₀⟩ := polynomial_ramified_analytic_root P A (ball 0 r) isOpen_ball
    hA' hlead hsep ⟨0,mem_ball_self hr⟩ unitImaginaryHalfPlane (b (0,t₁)) hroot₀
  let t₀ : ℝ := Real.exp (-2 * Real.pi / l)
  have htl : (0 : ℝ) < l := by exact_mod_cast hl
  have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 := halfPlaneQ_unitImaginary_real_bounds l htl
  have hpow : t₀^l = t₁ := by
    have he := congrArg Subtype.val (halfPlaneQ_nat l hl unitImaginaryHalfPlane)
    change (halfPlaneQ 1 one_pos unitImaginaryHalfPlane).val =
      (halfPlaneQ l htl unitImaginaryHalfPlane).val^l at he
    rw [halfPlaneQ_unitImaginary,halfPlaneQ_unitImaginary] at he
    dsimp only [t₀,t₁]
    exact_mod_cast he.symm
  have hinit : G (realParameter 0,t₀) = b (0,t₀^l) := by
    rw [hpow]
    rw [halfPlaneQ_unitImaginary] at hG₀
    simpa only [realParameter_zero,t₀] using hG₀
  have hmatch := ramified_real_branch_match P A hA'.continuousOn hlead hsep b hb hbr
    l hl G hGa.continuousOn hGr 0 (mem_ball_self hr) t₀ ht₀ hinit
  let K : (Fin n → ℂ) × ℂ → (Fin n → ℂ) × ℂ := fun p => (p.1,p.2^l)
  have hKa (p : (Fin n → ℂ) × ℂ) : AnalyticAt ℂ K p :=
    analyticAt_fst.prod (analyticAt_snd.pow l)
  have hK (p : (Fin n → ℂ) × ℂ) (hp : p ∈ ball 0 r ×ˢ ball 0 1) :
      K p ∈ ball 0 r ×ˢ ball 0 1 := by
    refine ⟨hp.1,?_⟩
    simp only [K,mem_ball,dist_zero_right,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by simpa only [mem_ball,dist_zero_right] using hp.2) hl.ne'
  have hAK : AnalyticOnNhd ℂ (A ∘ K) (ball 0 r ×ˢ ball 0 1) :=
    fun p hp => (hA (K p) (hK p hp)).comp (hKa p)
  have hpun : ball (0 : ℂ) 1 \ {0} = {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} := by
    ext u
    simp only [Set.mem_sdiff,mem_ball,dist_zero_right,mem_singleton_iff,mem_ofPred_eq,and_comm]
  obtain ⟨F,hFa,hFG⟩ := algebraic_real_parameter_removal P (A ∘ K) hr (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) < 1) hAK G (by simpa only [hpun] using hGa)
    (by simpa only [hpun,Function.comp_def,K] using hGr)
    (by
      intro p hp
      rw [hpun] at hp
      apply hlead (K p)
      exact ⟨hp.1,pow_ne_zero l hp.2.1,by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hp.2.2 hl.ne'⟩)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro s hs t ht ht1
      rw [hmatch s (by simpa only [mem_ball,dist_zero_right] using hs) t ⟨ht,ht1⟩]
      exact hbound (s,t^l) ⟨by simpa only [mem_ball,dist_zero_right] using hs,
        pow_pos ht l,pow_lt_one₀ ht.le ht1 hl.ne'⟩)
  refine ⟨l,hl,F,hFa,?_⟩
  intro s hs t ht
  rw [hFG (by
    refine ⟨realParameter_mem_ball hs,?_,?_⟩
    · simpa only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1] using ht.2
    · simpa only [mem_singleton_iff,Complex.ofReal_eq_zero] using ht.1.ne')]
  exact hmatch s hs t ⟨ht.1,ht.2.trans (by norm_num)⟩

end Release061

end

end OAI
