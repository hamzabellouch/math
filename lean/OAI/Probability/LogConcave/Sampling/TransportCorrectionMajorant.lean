import Mathlib
import OAI.Probability.LogConcave.Analysis.CenteringPotential
import OAI.Probability.LogConcave.JetEstimates.FlowJetMajorant
import OAI.Probability.LogConcave.Sampling.HarmonicKernel

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function TensorEnergy
open scoped NNReal BigOperators

lemma probabilityVelocity_iterated_small {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (probabilityVelocity F x r ρ) y))
      (((lam:ℝ)*r^2)*normalizedTensorMajorant (n+1) 1/R^(n-1)) := by
  have hh := (conditionalMean_iterated_uniform_split hF x hr hlam hl hρ0 hρ1 hR ha y (n:=n)).abs_const_mul (-r)
  rw [←multilinearTensor_const_smul (-r) _
    (conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1)] at hh
  change AllSplitBound _ _ at hh
  rw [abs_neg,abs_of_pos hr] at hh
  convert hh using 1 <;> first | rfl | ring

def transportCorrectionMajorant (n : ℕ) : ℝ := flowCorrectionMajorant
  (fun k => normalizedTensorMajorant (k+1) 1) (fun _ => normalizedTensorMajorant_nonneg _ _) n
lemma transportCorrectionMajorant_nonneg (n : ℕ) : 0≤transportCorrectionMajorant n :=
  flowCorrectionMajorant_nonneg _ _ _

theorem probabilityTransport_correction_split {d n : ℕ} (hn : 0<n)
    {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n
      (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z) y))
      (((lam:ℝ)*r^2)*transportCorrectionMajorant n/R^(n-1)) := by
  let a : ℝ := (t:ℝ)-(s:ℝ)
  let q (u : ℝ) := (s:ℝ)+a*u
  have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u∈Icc 0 T := by
    dsimp [q,a]
    constructor
    · nlinarith [s.2.1,t.2.1,mul_nonneg s.2.1 (sub_nonneg.mpr hu.2),mul_nonneg t.2.1 hu.1]
    · nlinarith [s.2.2,t.2.2,mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hu.2),
        mul_nonneg (sub_nonneg.mpr t.2.2) hu.1]
  have ha : |a|≤1 := (abs_le).mpr ⟨by dsimp [a]; linarith [t.2.1,s.2.2],by dsimp [a]; linarith [t.2.2,s.2.1]⟩
  let X (p : ℝ × Point d) := spatialTransport hF x hr.le hl hT0 hT1 s (q p.1,p.2)
  let V (u : ℝ) (z : Point d) := a • probabilityVelocity F x r (q u) z
  have hVX : TensorEnergy.SmoothTensorCurve d (fun k => normalizedTensorMajorant (k+1) 1) R 1 X V := by
    constructor
    · exact (spatialTransport_smooth hF x hr.le hl hT0 hT1 s).comp
        ((contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd)
    · intro z
      dsimp [X,q]
      simp only [mul_zero,add_zero]
      exact spatialTransport_initial hF x hr.le hl hT0 hT1 s z
    · intro u hu z
      have hd := (spatialTransport_deriv hF x hr.le hl hT0 hT1 s (hq u hu) z).scomp u
        ((hasDerivAt_const u (s:ℝ)).add ((hasDerivAt_const u a).mul (hasDerivAt_id u)))
      simpa only [zero_mul,one_mul,mul_one,zero_add,X,V,q,Function.comp_def] using hd
    · intro u hu
      exact (contDiff_const (c:=a)).smul ((contDiff_const (c:=(-r:ℝ))).smul
        (conditionalFieldMean_smooth hF x hr.le hl (hq u hu).1 ((hq u hu).2.trans_lt hT1)))
    · intro k u hu z
      have huT := hq u hu
      have hρ : R^2≤1-(q u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huT.2) (add_nonneg hT0 huT.1)]
      have hh := (probabilityVelocity_iterated_split hF x hr hlam hl huT.1
        (huT.2.trans_lt hT1) hR hρ z (n:=k)).abs_const_mul a
      have hvs : ContDiff ℝ (⊤:ℕ∞) (probabilityVelocity F x r (q u)) :=
        (contDiff_const (c:=(-r:ℝ))).smul (conditionalFieldMean_smooth hF x hr.le hl huT.1 (huT.2.trans_lt hT1))
      rw [←TensorEnergy.multilinearTensor_const_smul a (probabilityVelocity F x r (q u)) hvs z] at hh
      apply hh.mono (mul_nonneg (abs_nonneg _) (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)))
      exact mul_le_of_le_one_left (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)) ha
  have hv (k : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (z : Point d) :
      AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k (V u) z))
        (((lam:ℝ)*r^2)*normalizedTensorMajorant (k+1) 1/R^(k-1)) := by
    have huT := hq u hu
    have hρ : R^2≤1-(q u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huT.2) (add_nonneg hT0 huT.1)]
    have hh := (probabilityVelocity_iterated_small hF x hr hlam hl huT.1
      (huT.2.trans_lt hT1) hR hρ z (n:=k)).abs_const_mul a
    have hvs : ContDiff ℝ (⊤:ℕ∞) (probabilityVelocity F x r (q u)) :=
      (contDiff_const (c:=(-r:ℝ))).smul (conditionalFieldMean_smooth hF x hr.le hl huT.1 (huT.2.trans_lt hT1))
    rw [←multilinearTensor_const_smul a (probabilityVelocity F x r (q u)) hvs z] at hh
    have hp : 0≤((lam:ℝ)*r^2)*normalizedTensorMajorant (k+1) 1/R^(k-1) :=
      div_nonneg (mul_nonneg (mul_nonneg lam.coe_nonneg (sq_nonneg r))
        (normalizedTensorMajorant_nonneg _ _)) (pow_nonneg hR.le _)
    exact hh.mono (mul_nonneg (abs_nonneg _) hp) (mul_le_of_le_one_left hp ha)
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hh := smoothTensorCurve_correction hn (fun k => normalizedTensorMajorant (k+1) 1)
    (fun k => normalizedTensorMajorant_nonneg _ _) hR hR1 (by norm_num : (0:ℝ)≤1)
    le_rfl (mul_nonneg lam.coe_nonneg (sq_nonneg r)) X V hVX hv (t:=1) ⟨by norm_num,le_rfl⟩ y
  have he : (fun z => X (1,z))=probabilityTransport hF x hr.le hl hT0 hT1 s t := by
    funext z
    dsimp [X,q,a]
    rw [mul_one,add_sub_cancel]
    exact spatialTransport_eq hF x hr.le hl hT0 hT1 s t z
  have he' (z : Point d) : X (1,z)=probabilityTransport hF x hr.le hl hT0 hT1 s t z := congrFun he z
  simp_rw [he'] at hh
  exact hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

local instance : DecidableEq Unit := Classical.decEq _

def vectorArray {d : ℕ} (f : Point d → Point d) (c : Unit → Fin d) (y : Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ())) (f y)

lemma vectorArray_spatial {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) :
    spatialTensor (vectorArray f) (List.finRange n) y=
      fun c => multilinearTensor (iteratedFDeriv ℝ n f y) (c ∘ Equiv.sumComm Unit (Fin n)) := by
  funext c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (.inr ())))
  change JetCalculus.jet _ _ (L ∘ f) y=_
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hf),
    L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl

lemma vectorArray_polySmooth {d : ℕ} {f : Point d → Point d} {L : ℝ≥0}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hL : LipschitzWith L f)
    (M : ℕ → ℝ) (hM : ∀n,0≤M n)
    (hB : ∀n,0<n → ∀y,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n f y)) (M n))
    (c : Unit → Fin d) : PolySmooth (vectorArray f c) := by
  apply PolySmooth.of_basis_growth ((innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ()))).contDiff.comp hf)
  intro l
  by_cases hl : l=[]
  · subst l
    exact growth_of_lipschitz ((innerSL ℝ _).lipschitzWith.comp hL)
  · have hn : 0<l.length := List.length_pos_iff.mpr hl
    apply growth_of_bounded (hM l.length)
    intro y
    have hh := (hB l.length hn y).reindex (Equiv.sumComm Unit (Fin l.length))
    rw [←vectorArray_spatial hf y] at hh
    have hb := hh.entry_le (hM _) (by simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique]; omega)
      (Sum.elim l.get c)
    change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ l.get)
      (List.finRange l.length) (vectorArray f c) y|≤_ at hb
    rw [←JetCalculus.jet_map,List.map_get_finRange] at hb
    exact hb

lemma vectorArray_energy {d n : ℕ} {H : Point d → ℝ} {f : Point d → Point d}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (hp : ∀c,PolySmooth (vectorArray f c)) (hn : 0<n) {M : ℝ}
    (hB : ∀y,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n f y)) M) :
    spatialEnergy (vectorArray f) n (gibbs H)≤d*M^2 := by
  let := probability_gibbs_of_gaussianTail hH ht
  apply spatialEnergy_from_split hH ht _ hp hn
  intro y
  rw [vectorArray_spatial hf y]
  exact (hB y).reindex (Equiv.sumComm Unit (Fin n))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

local instance : DecidableEq Unit := Classical.decEq _

lemma probabilityTransport_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    LipschitzWith ⟨Real.exp (((Real.pi^2/2)*(lam:ℝ)*r^2)*|(t:ℝ)-(s:ℝ)|),(Real.exp_pos _).le⟩
      (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  GlobalODE.flow_lipschitz _ _ s t

lemma probabilityTransport_infty {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  contDiff_infty.mpr (probabilityTransport_contDiff hF x hr hl hT0 hT1 s t)

lemma probabilityCorrection_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) :
    ∀c,PolySmooth (vectorArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z) c) :=
  vectorArray_polySmooth ((probabilityTransport_infty hF x hr.le hl hT0 hT1 s t).sub contDiff_id)
    ((probabilityTransport_lipschitz hF x hr.le hl hT0 hT1 s t).sub LipschitzWith.id)
    (fun n => ((lam:ℝ)*r^2)*transportCorrectionMajorant n/R^(n-1))
    (fun n => div_nonneg (mul_nonneg (mul_nonneg lam.2 (sq_nonneg r)) (transportCorrectionMajorant_nonneg n))
      (pow_nonneg hR.le _))
    (fun _ hn => probabilityTransport_correction_split hn hF x hr hlam hl hR hRT hT0 hT1 s t)

lemma probabilityCorrection_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (u : Icc (0:ℝ) T) (hn : 0<n) :
    spatialEnergy (vectorArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)) n
      (gibbs (interpolationPotential F x r u))≤
      d*((lam:ℝ)*r^2)^2*(transportCorrectionMajorant n/R^(n-1))^2 := by
  have hh := vectorArray_energy
    (interpolationPotential_smooth hF x hr.le hl u.2.1 (u.2.2.trans_lt hT1)).continuous
    (interpolationPotential_lowerTail hF x hr.le (by linarith) u.2.1 (u.2.2.trans_lt hT1))
    ((probabilityTransport_infty hF x hr.le hl hT0 hT1 s t).sub contDiff_id)
    (probabilityCorrection_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t) hn
    (probabilityTransport_correction_split hn hF x hr hlam hl hR hRT hT0 hT1 s t)
  exact hh.trans_eq (by ring)

def jointCorrectionArray {d : ℕ} (f : Point d → Point d) :
    (Unit → Fin (d+d)) → Point (d+d) → ℝ :=
  arrayCoordinateLift (leftCoordinates d d) (fun _ => leftCoordinates d d) (vectorArray f)

lemma jointCorrectionArray_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (u : Icc (0:ℝ) T) (hn : 0<n) :
    spatialEnergy (jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)) n
      (gibbs (centeringPotential F x r u))≤
      d*((lam:ℝ)*r^2)^2*(transportCorrectionMajorant n/R^(n-1))^2 := by
  have hH := interpolationPotential_polySmooth hF x hr hlam hl u.2.1 (u.2.2.trans_lt hT1)
  have ht := interpolationPotential_lowerTail hF x hr.le (by linarith) u.2.1 (u.2.2.trans_lt hT1)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  dsimp only [jointCorrectionArray,centeringPotential]
  rw [spatialEnergy_leftLift hH.smooth.continuous _
    (fun c => (probabilityCorrection_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t c).smooth)]
  exact probabilityCorrection_energy hF x hr hlam hl hR hRT hT0 hT1 s t u hn
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

local instance : DecidableEq Unit := Classical.decEq _

lemma normalizedTensorMajorant_inv_scale {k : ℕ} {R a : ℝ}
    (hR : 0<R) (hR1 : R≤1) (ha : R^2≤a) :
    normalizedTensorMajorant (k+1) a≤normalizedTensorMajorant (k+1) 1*(R⁻¹)^k := by
  have hh := normalizedTensorMajorant_scale (n:=k+1) hR ha
  have hp : R^k≤R^(k+1-2) := pow_le_pow_of_le_one hR.le hR1 (by omega)
  apply hh.trans
  rw [inv_pow,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (normalizedTensorMajorant_nonneg _ _) (pow_pos hR _) hp

lemma inv_scale_pred {R A : ℝ} (hR : 0<R) (hR1 : R≤1) (hA : 0≤A) (k : ℕ) :
    A/R^(k-1)≤A*(R⁻¹)^k := by
  rw [inv_pow,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hA (pow_pos hR _) (pow_le_pow_of_le_one hR.le hR1 (by omega))

def harmonicGradientBound : ℝ≥0 := ⟨2+Real.pi^2,by positivity⟩

lemma centeringPotential_gradient_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ}
    (hr : 0<r) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    LipschitzWith harmonicGradientBound (gradient (centeringPotential F x r T)) := by
  apply (centeringPotential_gradient_lipschitz hF x hr hl hT0 hT1).weaken
  change (1+‖r*T‖*((Real.pi^2/2)*T*((lam:ℝ)*r)))+1≤2+Real.pi^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le hT0)]
  have hl0 : 0≤(lam:ℝ)*r^2 := mul_nonneg lam.2 (sq_nonneg r)
  have hT : T^2≤1 := by nlinarith
  have hb : (lam:ℝ)*r^2*T^2≤1/2 := by
    calc
      _ ≤ (lam:ℝ)*r^2*1 := mul_le_mul_of_nonneg_left hT hl0
      _ ≤ _ := by simpa only [mul_one] using hl
  have hp := mul_le_mul_of_nonneg_left hb (sq_nonneg Real.pi)
  nlinarith [sq_nonneg Real.pi]

lemma harmonicSkew_inv_scaled {d : ℕ} {R : ℝ} (hR : 0<R) (hR1 : R≤1) :
    ∀k y,AllSplitBound (spatialTensor (harmonicSkew d) (List.finRange k) y)
      ((2:ℝ)*1*(R⁻¹)^k) := by
  intro k y
  have hh := harmonicSkew_scaled_bound d k y
  apply hh.mono (by norm_num)
  have hi : 1≤R⁻¹ := (one_le_inv₀ hR).mpr hR1
  simpa only [mul_one,one_pow] using mul_le_mul_of_nonneg_left (one_le_pow₀ hi) (by norm_num : (0:ℝ)≤2)

lemma centeringScore_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField (centeringPotential F x r T))
      (List.finRange k) y) ((2+normalizedTensorMajorant (k+1) 1)*(R⁻¹)^k) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hi : 1≤R⁻¹ := (one_le_inv₀ hR).mpr hR1
  intro k hk y
  have hh := centeringScore_scaled_bound hF x hr hlam hl hT0 hT1 k hk y
  simp only [one_pow,mul_one] at hh
  apply hh.mono (add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _))
  have he := normalizedTensorMajorant_inv_scale (k:=k) hR hR1 hRT
  have hp : (2:ℝ)≤2*(R⁻¹)^k := by nlinarith [one_le_pow₀ hi (n:=k)]
  nlinarith

lemma centeringMean_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → spatialEnergy (centeringMeanArray F x r T) k (gibbs (centeringPotential F x r T))≤
      (d*((lam:ℝ)*r)^2)*(R⁻¹)^(2*k)*(normalizedTensorMajorant (k+1) 1)^2 := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  intro k hk
  apply (centeringMeanArray_energy hF x hr hlam hl hT0 hT1 hk).trans
  have he := pow_le_pow_left₀ (normalizedTensorMajorant_nonneg (k+1) (1-T^2))
    (normalizedTensorMajorant_inv_scale (k:=k) hR hR1 hRT) 2
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(d:ℝ)*((lam:ℝ)*r)^2 by positivity)
  convert hh using 1; first | rfl | simp only [mul_pow,←pow_mul]; ring

lemma jointCorrection_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t u : Icc (0:ℝ) T) :
    ∀k,0<k → spatialEnergy
      (jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)) k
      (gibbs (centeringPotential F x r u))≤
      (d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(2*k)*(transportCorrectionMajorant k)^2 := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  intro k hk
  apply (jointCorrectionArray_energy hF x hr hlam hl hR hRT hT0 hT1 s t u hk).trans
  have he := pow_le_pow_left₀ (div_nonneg (transportCorrectionMajorant_nonneg k) (pow_nonneg hR.le _))
    (inv_scale_pred hR hR1 (transportCorrectionMajorant_nonneg k) k) 2
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(d:ℝ)*((lam:ℝ)*r^2)^2 by positivity)
  convert hh using 1; first | rfl | simp only [mul_pow,←pow_mul]; ring
end LogConcaveSampling

end

end

end

end OAI
