import OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import OAI.NumberTheory.DirichletL.Energy.Bands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open HeckeFamily HeckeDetectorRawFiber CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainStateDictionary
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O

def allowance (δ m:ℝ):ℝ:=δ+max 0 (2*m-1)

lemma allowance_nonneg (δ m:ℝ)(hδ:0≤δ):0≤allowance δ m:=
  add_nonneg hδ (le_max_left _ _)

lemma padded_width (δ m:ℝ):1+allowance δ m=max 1 (2*m)+δ:=by
  unfold allowance
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right (by linarith:0≤2*m-1)]
    ring
  · rw [max_eq_left (le_of_not_ge hm),max_eq_left (by linarith:2*m-1≤0)]
    ring

lemma padded_modulus (η:Character)(U δ m:ℝ)(hU:1≤U)
    (hη:(η.modulus.absNorm:ℝ)≤U^δ):
    (η.modulus.absNorm:ℝ)≤U^(allowance δ m):=
  hη.trans (Real.rpow_le_rpow_of_exponent_le hU (le_add_of_nonneg_right (le_max_left _ _)))

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T heightAllowance:ℝ}{i:ℕ}

def state (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState U 0 bΦ:=
  initialState η Q Φ bΦ U (allowance δ F.m) hU (allowance_nonneg _ _ hδ) hs hp
    (padded_modulus η U δ F.m hU hη)

omit [NeZero M] in
theorem actual_scale_gates (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ εcap:ℝ)
    (hU:1<U)(hδ:0≤δ)(hε:ε≤εcap)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):
    let s:=state F η Q Φ bΦ δ hU.le hδ hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+δ ∧
    s.width≤max 1 (1+150*εcap)+δ ∧
    1≤U^F.m ∧ length U (U^F.m)=F.m ∧
    2*length U (U^F.m)≤s.width ∧ U^F.m≤U^(1/2+75*εcap):=by
  dsimp only
  have hm:=F.lengths hU
  have hmcap:F.m≤1/2+75*εcap:=by linarith [hm.2.2.1]
  have hscale:1≤U^F.m:=Real.one_le_rpow hU.le hm.2.2.2.2
  have hlen:length U (U^F.m)=F.m:=by
    rw [length,max_eq_right hscale]
    exact Real.logb_rpow (zero_lt_one.trans hU) hU.ne'
  have hw:(state F η Q Φ bΦ δ hU.le hδ hs hp hη).width=max 1 (2*F.m)+δ:=padded_width δ F.m
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,hw,?_,hscale,hlen,?_,?_⟩
  · rw [hw]
    exact add_le_add (max_le_max le_rfl (by linarith)) le_rfl
  · rw [hw,hlen]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right hδ)
  · exact Real.rpow_le_rpow_of_exponent_le hU.le hmcap

omit [NeZero M] in
theorem actual_source_eq (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (state F η Q Φ bΦ δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=
  retainedSourceEnergy_empty_eq_plainEnergy F η Q Φ bΦ (allowance δ F.m)
    hU (allowance_nonneg _ _ hδ) hs hp (padded_modulus η U δ F.m hU hη) j k σ t

end SevenEighths.CenteredMomentDetectorPlainUnmarkedState

end

end OAI
