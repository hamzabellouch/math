import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}

def delta (D:Parameters.HighData Δ):ℝ := D.t/4
def stageError (D:Parameters.HighData Δ):ℝ := D.t/4
def kappaPlain (_D:Parameters.HighData Δ):ℝ := 3/4+2*Δ

theorem fixed_parameters (D:Parameters.HighData Δ):
    0<delta D ∧ delta D≤1/4 ∧ 0<stageError D ∧
    delta D+stageError D≤D.t ∧ 3/4<kappaPlain D ∧ 0<kappaPlain D := by
  have hΔ:0<Δ:=by linarith [D.t_pos,D.t_delta]
  dsimp [delta,stageError,kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma source_base_gt_one (_D:Parameters.HighData Δ)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d):1<Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (D:Parameters.HighData Δ):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

lemma original_width_bounds (D:Parameters.HighData Δ)(d:ℝ)
    (hd:(1/200:ℝ)≤d)(s:Fin D.N):0<D.ell s/d ∧ D.ell s/d≤D.t := by
  have hdpos:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds s).1 hdpos,(div_le_iff₀ hdpos).mpr ?_⟩
  have hs: D.ell s≤(1/200:ℝ)*D.t:=(D.slots_bounds s).2.2
  nlinarith [D.t_pos]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1<U):
    0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact plain_length_eq F hU

theorem batch_fiber_parameters (D:Parameters.HighData Δ)(Z d:ℝ)
    (hZ:1<Z)(hd:(1/200:ℝ)≤d)
    (B:Batch M H Label (Fin D.N) (Z^d) a D.ε tstar T heightAllowance i)
    (hwidth:B.widths=(fun s=>D.ell s/d))
    (bin label J K)(hne:(B.fiberRows bin label J K).Nonempty):
    let F:=B.fiber bin label J K hne;
    1<Z^d ∧ 0≤F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤(Z^d)^F.m ∧ (Z^d)^F.m≤Z^d ∧ length (Z^d) ((Z^d)^F.m)=F.m ∧
    (∀s,0<F.widths s ∧ F.widths s≤D.t) ∧
    (∀selected:Finset (Fin D.N),∀s:selected,0<F.widths s.val ∧ F.widths s.val≤D.t) := by
  dsimp only
  have hU:=source_base_gt_one D Z d hZ hd
  have hf:=actual_fiber_lengths D (B.fiber bin label J K hne) hU
  have hw:∀s,0<(B.fiber bin label J K hne).widths s ∧
      (B.fiber bin label J K hne).widths s≤D.t:=by
    intro s
    change 0<B.widths s ∧ B.widths s≤D.t
    rw [hwidth]
    exact original_width_bounds D d hd s
  exact ⟨hU,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    hw,fun _ s=>hw s.val⟩

lemma width_bands (D:Parameters.HighData Δ)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0<delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain D)*(∑s:selected,F.widths s.val)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact marked_capacity F hU selected (kappaPlain D) (delta D) (fixed_parameters D).1.le hcap

theorem unmarked_state_admission (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1<U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤s.width ∧ s.width≤2 ∧
    1≤U^F.m ∧ U^F.m≤U ∧ 2*length U (U^F.m)≤s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters D).1.le)

theorem source_label_fixed_allowance (D:Parameters.HighData Δ)
    (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget (D:Parameters.HighData Δ)(base:ℝ):
    base+delta D+stageError D≤base+D.t := by
  linarith [(fixed_parameters D).2.2.2.1]

end SevenEighths.CenteredMomentDetectorPlainMomentParameters

end

end OAI
