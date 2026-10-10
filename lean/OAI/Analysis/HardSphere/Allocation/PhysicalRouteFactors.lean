import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalRouteGeometry
import OAI.Analysis.HardSphere.Bridges.PhysicalEndpoint

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

def pointAsPath (u : Point) : C(Time,Point) := ContinuousMap.const Time u

lemma pointAsPath_measurable : Measurable pointAsPath := by
  apply Continuous.measurable
  exact ContinuousMap.continuous_const'

@[simp] lemma pointAsPath_apply (u : Point) (s : Time) : pointAsPath u s=u := rfl

def cellPathReference {K : ℕ} (v : Fin 3→Fin K) : Measure C(Time,Point) :=
  (targetUniform (unitTarget (anchorPoint v))).map pointAsPath

instance cellPathReference_probability {K : ℕ} (v : Fin 3→Fin K) :
    IsProbabilityMeasure (cellPathReference v) := by
  have : IsProbabilityMeasure (targetUniform (unitTarget (anchorPoint v))) := by
    rw [targetUniform,unitTarget_volume,inv_one,one_smul]
    constructor
    simp only [Measure.restrict_apply_univ,unitTarget_volume]
  unfold cellPathReference
  infer_instance

def routeDensityBound (t : ℝ) : ℝ≥0∞ := max 2 (vertexDensityBound t)

lemma vertex_le_routeDensity (t : ℝ) : vertexDensityBound t≤routeDensityBound t := le_max_right _ _
lemma endpoint_le_routeDensity (t : ℝ) :
    (ENNReal.ofReal (49/50:ℝ))⁻¹≤routeDensityBound t := by
  apply le_trans _ (le_max_left _ _)
  rw [←ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<49/50)]
  norm_num

def encodeFirstEndpoint (p : C(Time,Point)×Point) : C(Time,Point)×C(Time,Point) :=
  (p.1,pointAsPath p.2)
def encodeLastEndpoint (p : C(Time,Point)×Point) : C(Time,Point)×C(Time,Point) :=
  (pointAsPath p.2,p.1)
lemma encodeFirstEndpoint_measurable : Measurable encodeFirstEndpoint :=
  measurable_fst.prodMk (pointAsPath_measurable.comp measurable_snd)
lemma encodeLastEndpoint_measurable : Measurable encodeLastEndpoint :=
  (pointAsPath_measurable.comp measurable_snd).prodMk measurable_fst

lemma encoded_endpoint_physical {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (hc : projectPoint L (routeCellPeriod v w j)=0)
    (d : PhysicalDatum N K M G L) (hw : datumHome hL d i=w)
    (hi : datumAccessible hL g m t r R C S u i d) :
    let ρ := endpointPair hL g m t r R C S u i v w j d
    let P := datumIndividualReference hL g m r R C S t u i d
    let ρ₀ := ρ.map encodeFirstEndpoint
    let ρ₁ := ρ.map encodeLastEndpoint
    IsProbabilityMeasure ρ₀ ∧ IsProbabilityMeasure ρ₁ ∧ IsProbabilityMeasure P ∧
      ρ₀.fst≤routeDensityBound t • P ∧ ρ₀.snd≤routeDensityBound t • cellPathReference v ∧
      ρ₁.fst≤routeDensityBound t • cellPathReference v ∧ ρ₁.snd≤routeDensityBound t • P ∧
      (∀ᵐp ∂ρ₀,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) ∧
      (∀ᵐp ∂ρ₁,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  obtain ⟨hρ,hP,hfst,hsnd,hmid⟩ := endpointPair_physical hL g m t r R C S ht u i v w j hc d hw hi
  let ρ := endpointPair hL g m t r R C S u i v w j d
  have : IsProbabilityMeasure ρ := hρ
  have F : (ρ.map encodeFirstEndpoint).fst=ρ.fst := by
    rw [Measure.fst,Measure.map_map measurable_fst encodeFirstEndpoint_measurable]
    rfl
  have HS : (ρ.map encodeFirstEndpoint).snd=ρ.snd.map pointAsPath := by
    rw [Measure.snd,Measure.map_map measurable_snd encodeFirstEndpoint_measurable,
      Measure.snd,Measure.map_map pointAsPath_measurable measurable_snd]
    rfl
  have F' : (ρ.map encodeLastEndpoint).fst=ρ.snd.map pointAsPath := by
    rw [Measure.fst,Measure.map_map measurable_fst encodeLastEndpoint_measurable,
      Measure.snd,Measure.map_map pointAsPath_measurable measurable_snd]
    rfl
  have HS' : (ρ.map encodeLastEndpoint).snd=ρ.fst := by
    rw [Measure.snd,Measure.map_map measurable_snd encodeLastEndpoint_measurable]
    rfl
  have HB : ρ.snd.map pointAsPath≤routeDensityBound t • cellPathReference v := by
    have H := Measure.map_mono hsnd pointAsPath_measurable
    rw [Measure.map_smul _ pointAsPath_measurable.aemeasurable] at H
    exact H.trans (by dsimp only [cellPathReference]; gcongr; exact endpoint_le_routeDensity t)
  have HP : ρ.fst≤routeDensityBound t • datumIndividualReference hL g m r R C S t u i d :=
    hfst.trans (by gcongr; exact vertex_le_routeDensity t)
  refine ⟨inferInstance,inferInstance,hP,?_,?_,?_,?_,?_,?_⟩
  · rw [F];exact HP
  · rw [HS];exact HB
  · rw [F'];exact HB
  · rw [HS'];exact HP
  · rw [ae_map_iff encodeFirstEndpoint_measurable.aemeasurable (by measurability)]
    exact hmid
  · rw [ae_map_iff encodeLastEndpoint_measurable.aemeasurable (by measurability)]
    filter_upwards [hmid] with p hp
    exact hp.symm

def physicalRouteFactor {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (k : Fin (n+2)) :
    Kernel (PhysicalDatum N K M G L) (C(Time,Point)×C(Time,Point)) :=
  if h0 : k.val=0 then
    (endpointPair hL g m t r R C S u (labels 0) (v 0) (v 0) 0).map encodeFirstEndpoint
  else if hk : k.val<n+1 then
    vertexPair hL g m t r R C S u (labels ⟨k.val,hk⟩)
      (labels ⟨k.val-1,by omega⟩) (v k) (v ⟨k.val-1,by omega⟩) (steps ⟨k.val-1,by omega⟩)
  else
    (endpointPair hL g m t r R C S u (labels (Fin.last n)) (v (Fin.last (n+1)))
      (v (Fin.last n).castSucc) (steps (Fin.last n))).map encodeLastEndpoint

instance physicalRouteFactor_finite {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (k : Fin (n+2)) :
    IsFiniteKernel (physicalRouteFactor (M:=M) hL g m t r R C S u labels v steps k) := by
  unfold physicalRouteFactor
  split_ifs <;> infer_instance

def routeFirstReference {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) : Measure C(Time,Point) :=
  if hk : k.val<n+1 then datumIndividualReference hL g m r R C S t u (labels ⟨k.val,hk⟩) d
  else cellPathReference (v k)

def routeSecondReference {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (k : Fin (n+2)) (d : PhysicalDatum N K M G L) : Measure C(Time,Point) :=
  if h0 : k.val=0 then cellPathReference (v k)
  else datumIndividualReference hL g m r R C S t u (labels ⟨k.val-1,by omega⟩) d

theorem physicalRouteFactor_physical {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (labels k)=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (labels k) d)
    (k : Fin (n+2)) :
    let ρ := physicalRouteFactor hL g m t r R C S u labels v steps k d
    let P := routeFirstReference hL g m t r R C S u labels v k d
    let Q := routeSecondReference hL g m t r R C S u labels v k d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      ρ.fst≤routeDensityBound t • P ∧ ρ.snd≤routeDensityBound t • Q ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  by_cases h0 : k.val=0
  · have hk : k=0 := Fin.ext h0
    subst k
    have H := encoded_endpoint_physical hL g m t r R C S ht u (labels 0) (v 0) (v 0) 0
      (self_routeCellPeriod (v 0)) d (hhome 0) (haccess 0)
    simp only [physicalRouteFactor,routeFirstReference,routeSecondReference,Fin.val_zero,
      Nat.zero_lt_succ,↓reduceDIte,Kernel.map_apply _ encodeFirstEndpoint_measurable]
    exact ⟨H.1,H.2.2.1,inferInstance,H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2.2.2.1⟩
  · by_cases hk : k.val<n+1
    · let i : Fin (n+1) := ⟨k.val,hk⟩
      let j : Fin (n+1) := ⟨k.val-1,by omega⟩
      have hi : i.castSucc=k := Fin.ext rfl
      have hj : j.succ=k := Fin.ext (by dsimp [j];omega)
      have he : projectPoint L (routeCellPeriod (v k) (v j.castSucc) (steps j))=0 := by
        simpa only [hj] using hc j
      obtain ⟨hρ,hP,hQ,hF,hS,hmid⟩ := vertexPair_physical hL g m t r R C S ht u
        (labels i) (labels j) (v k) (v j.castSucc) (steps j) he d
        (by simpa only [hi] using hhome i) (hhome j) (haccess i) (haccess j)
      simp only [physicalRouteFactor,routeFirstReference,routeSecondReference,dite_eq_right h0,dite_eq_left hk]
      exact ⟨hρ,hP,hQ,hF.trans (by gcongr;exact vertex_le_routeDensity t),
        hS.trans (by gcongr;exact vertex_le_routeDensity t),hmid⟩
    · have he : k=Fin.last (n+1) := Fin.ext (by simp only [Fin.val_last];omega)
      subst k
      have H := encoded_endpoint_physical hL g m t r R C S ht u (labels (Fin.last n))
        (v (Fin.last (n+1))) (v (Fin.last n).castSucc) (steps (Fin.last n))
        (hc (Fin.last n)) d (hhome (Fin.last n)) (haccess (Fin.last n))
      have hl : (⟨(n+1)-1,by omega⟩ : Fin (n+1))=Fin.last n := Fin.ext (by simp)
      simp only [physicalRouteFactor,routeFirstReference,routeSecondReference,
        Fin.val_last,Nat.add_one_ne_zero,Nat.lt_irrefl,↓reduceDIte,hl,Kernel.map_apply _ encodeLastEndpoint_measurable]
      exact ⟨H.2.1,inferInstance,H.2.2.1,H.2.2.2.2.2.1,H.2.2.2.2.2.2.1,H.2.2.2.2.2.2.2.2⟩

end HardSphere.Groups
end
end

end OAI
