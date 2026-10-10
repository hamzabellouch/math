import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerState
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerRanges
import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

def fullPunctureWidth (Z:ℝ)(t:Ideal O)(j:O):ℝ :=
  Real.logb Z (Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)

theorem full_puncture_width_exact (Z:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0):
    0≤fullPunctureWidth Z t j ∧
      ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) := by
  have hn:(1:ℝ)≤Ideal.absNorm (Ideal.span {j*primaryGenerator t}) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  constructor
  · unfold fullPunctureWidth Real.logb
    exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le
  · rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (zero_lt_one.trans_le hn)).symm

theorem full_product_width_bound (Z P G η:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0)
    (hspan:Ideal.span {j*primaryGenerator t}=t*Ideal.span {j})
    (ht:(t.absNorm:ℝ)≤Z^(P+2*η))
    (hj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η)):
    fullPunctureWidth Z t j≤P+G+3*η := by
  have hz:=zero_lt_one.trans hZ
  have hpos:0<(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  have hb:(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)≤Z^(P+G+3*η):=by
    rw [hspan,map_mul,Nat.cast_mul]
    apply (mul_le_mul ht hj (by positivity) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  unfold fullPunctureWidth Real.logb
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  simpa only [Real.log_rpow hz] using Real.log_le_log hpos hb

theorem physical_row_width_le (m r z G B θ H η τ:ℝ)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    θ+H+2*η≤ initialM m r z G (B-θ) η τ := by
  unfold radialCenter at hcut
  unfold initialM
  linarith

theorem enlarged_initial_margins (m r z G B θ v H η τ Q c₁ c₂:ℝ)
    (h₁:r+2*z≤m-c₁)(h₂:2*r+8*z≤3*m-c₂)
    (hG:0≤G)(hP:-2*η≤B-θ)(hQ:Q≤B-θ+G+3*η)
    (hc:0≤min c₁ c₂)(hη:0≤η)(hηsmall:η≤min c₁ c₂/100)
    (hτ:τ≤min c₁ c₂/100)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    CanonicalMargins
      (max 0 (r+z-2*G-B-v)+(θ+v+2*η)) (θ+H+2*η) Q (z-G)
      (3*min c₁ c₂/4) := by
  have hd:0≤max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v):=
    sub_nonneg.mpr (le_max_right _ _)
  have hh:=initial_margins (delta:=max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v))
    h₁ h₂ hG hP hQ hc hd hηsmall hτ
  have hr:=physical_row_width_le m r z G B θ H η τ hcut
  unfold CanonicalMargins at hh ⊢
  unfold initialF at hh
  constructor <;> linarith [hh.1,hh.2]

theorem enlarged_label_exact (N V η:ℝ)(hV:0≤V+2*η):
    max 0 (V+2*η)=V+2*η ∧
      N+max 0 (V+2*η)-(N+V)=2*η := by
  rw [max_eq_right hV]
  exact ⟨rfl,by ring⟩

theorem assigned_label_weight_le {σ:Type*}[DecidableEq σ]
    (slots J₁ J₂:Finset σ)(K:ℕ)(hK:slots.card≤K)
    (h₁:J₁⊆slots)(h₂:J₂⊆slots)(f:Ideal O)(hf:f≠0):
    ((IdealMobiusDivisorSum.idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)≤secondLabelWeight K f := by
  have hmem:(1:Ideal O)∈IdealMobiusDivisorSum.idealDivisors f:=
    (IdealMobiusDivisorSum.mem_idealDivisors hf).mpr (one_dvd _)
  have hn:(1:ℝ)≤(IdealMobiusDivisorSum.idealDivisors f).card:=by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hmem⟩
  have hcard1:=Finset.card_le_card h₁
  have hcard2:=Finset.card_le_card h₂
  exact pow_le_pow_right₀ hn (by omega)

end SevenEighths.InverseInitialCanonicalState

end

end OAI
