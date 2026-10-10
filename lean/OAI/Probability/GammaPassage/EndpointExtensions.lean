import OAI.Probability.GammaPassage.EndpointEntrance
import OAI.Probability.GammaPassage.EndpointExit
import OAI.Probability.GammaPassage.EndpointBounds

namespace OAI

/-! Whole entrance and exit paths for Lemma `gr:variable-endpoints`. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set

noncomputable def endpointBox (b A R : ℝ) (k m : ℕ) : Set Vertex :=
  {z | |(z.1 : ℝ)| ≤ A*(2 : ℝ)^m ∧ |transverse b z| ≤ R*(2 : ℝ)^k}

/-- Entrance and exit extensions with cost and enlarged-localization
bounds, simultaneously for every lattice vertex in the box. -/
theorem gridConnections_endpoint_extensions (w : Edge → ℝ) (shape rate b m₀ K A R : ℝ)
    (hshape : 0 < shape) (hrate : 0 < rate) (hK : 100 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m)
    (hlast : gridLastLevel m ≤ k)
    (hg : w ∈ gridConnectionsEvent shape rate b m₀ K A R k m J)
    (p : Vertex) (hp : p ∈ endpointBox b A R k m) :
    ColumnConnection w b (transverse b p) m₀ (endpointExtensionError shape rate K k J)
      (endpointBox b (A+4) (R+2*(Grid.attachmentAllowance shape rate K)) k m) (entranceColumn p.1 m J) p.1 ∧
    ColumnConnection w b (transverse b p) m₀ (endpointExtensionError shape rate K k J)
      (endpointBox b (A+4) (R+2*(Grid.attachmentAllowance shape rate K)) k m) p.1 (exitColumn p.1 m J) := by
  have hallow : 50 ≤ Grid.attachmentAllowance shape rate K :=
    Grid.attachmentAllowance_ge_fifty hshape hrate hK
  let H := 2*(Grid.attachmentAllowance shape rate K)*(2 : ℝ)^k
  have hH : 1 ≤ H := by
    have hs := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
    dsimp [H]
    nlinarith
  have herr (j : ℕ) (_hj : J ≤ j) (hjl : j ≤ gridLastLevel m) :
      (Grid.attachmentAllowance shape rate K)*(j : ℝ)^2*gridWidth k j ≤ H := grid_endpoint_height shape rate K hshape hrate hK k j (hjl.trans hlast)
  have hd := gridMesh_pos m J
  have hdR : (0 : ℝ) < gridMesh m J := by exact_mod_cast hd
  have hmesh := gridMesh_le_scale m J
  have hL : (0 : ℝ) < 2^m := by positivity
  have hs := entranceColumn_span p.1 m J
  have ht := exitColumn_span p.1 m J
  have hsR : (gridMesh m J : ℝ) ≤ (p.1 : ℝ)-(entranceColumn p.1 m J : ℝ) ∧
      (p.1 : ℝ)-(entranceColumn p.1 m J : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast hs
  have htR : (gridMesh m J : ℝ) ≤ (exitColumn p.1 m J : ℝ)-(p.1 : ℝ) ∧
      (exitColumn p.1 m J : ℝ)-(p.1 : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast ht
  have hpx := abs_le.mp hp.1
  have hleft : -(A+4)*(2 : ℝ)^m ≤ (entranceColumn p.1 m J : ℝ) := by linarith [hsR.2]
  have hright : (exitColumn p.1 m J : ℝ) ≤ (A+4)*(2 : ℝ)^m := by linarith [htR.2]
  have hpL : -(A+4)*(2 : ℝ)^m ≤ (p.1 : ℝ) := by linarith [hpx.1]
  have hpR : (p.1 : ℝ) ≤ (A+4)*(2 : ℝ)^m := by linarith [hpx.2]
  have hentr := gridConnections_entrance w shape rate b m₀ K A R H hshape hrate hK hH k m J hJ hJlast hg herr p hleft hpR hp.2
  have hexit := gridConnections_exit w shape rate b m₀ K A R H hshape hrate hK hH k m J hJ hJlast hg herr p hpL hright hp.2
  have hc := endpoint_extension_cost_sum shape rate K hshape hrate hK k m J hlast hJlast
  constructor
  · have hconn : ColumnConnection w b (transverse b p) m₀
        (∑ i ∈ Finset.range (gridLastLevel m-J+1),16*((Grid.attachmentAllowance shape rate K)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
        (endpointTube b (transverse b p) H (entranceColumn p.1 m J-gridMesh m J) (p.1+gridMesh m J))
        (entranceColumn p.1 m J) p.1 := by
      simpa only [ColumnConnection,endpointVertex_self] using hentr
    apply ColumnConnection.mono hconn hc
    intro z hz
    apply endpoint_localization b A R (Grid.attachmentAllowance shape rate K) (by linarith) k m p z (gridMesh m J) hmesh hp.1 hp.2
    · exact ⟨by have hh := hz.1; omega,
        by have hh := hz.2.1; omega⟩
    · exact hz.2.2
  · have hconn : ColumnConnection w b (transverse b p) m₀
        (∑ i ∈ Finset.range (gridLastLevel m-J+1),16*((Grid.attachmentAllowance shape rate K)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
        (endpointTube b (transverse b p) H (p.1-gridMesh m J) (exitColumn p.1 m J+gridMesh m J))
        p.1 (exitColumn p.1 m J) := by
      simpa only [ColumnConnection,endpointVertex_self] using hexit
    apply ColumnConnection.mono hconn hc
    intro z hz
    apply endpoint_localization b A R (Grid.attachmentAllowance shape rate K) (by linarith) k m p z (gridMesh m J) hmesh hp.1 hp.2
    · exact ⟨by have hh := hz.1; omega,
        by have hh := hz.2.1; omega⟩
    · exact hz.2.2

/-- Defect bounds for either supporting slope. The fixed-target floor
error is paid once for each whole attachment. -/
theorem gridConnections_endpoint_defects (w : Edge → ℝ) (shape rate b m₀ K A R : ℝ)
    (hshape : 0 < shape) (hrate : 0 < rate) (hK : 100 ≤ K) (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m)
    (hlast : gridLastLevel m ≤ k)
    (hg : w ∈ gridConnectionsEvent shape rate b m₀ K A R k m J)
    (p : Vertex) (hp : p ∈ endpointBox b A R k m) :
    ∃ ds es,
      endpointVertex b (transverse b p) (entranceColumn p.1 m J)+displacement ds=p ∧
      p+displacement es=endpointVertex b (transverse b p) (exitColumn p.1 m J) ∧
      (∀ a : ℝ, defect w b m₀ a (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds ≤
        endpointExtensionError shape rate K k J+|a|) ∧
      (∀ a : ℝ, defect w b m₀ a p es ≤ endpointExtensionError shape rate K k J+|a|) ∧
      PathIn (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds
        (endpointBox b (A+4) (R+2*(Grid.attachmentAllowance shape rate K)) k m) ∧
      PathIn p es (endpointBox b (A+4) (R+2*(Grid.attachmentAllowance shape rate K)) k m) := by
  obtain ⟨⟨ds,hd,hc,hin⟩,⟨es,he,hce,hine⟩⟩ :=
    gridConnections_endpoint_extensions w shape rate b m₀ K A R hshape hrate hK k m J hJ hJlast hlast hg p hp
  refine ⟨ds,es,by simpa only [endpointVertex_self] using hd,
    by simpa only [endpointVertex_self] using he,?_,?_,hin,by simpa only [endpointVertex_self] using hine⟩
  · intro a
    exact endpoint_path_defect w b (transverse b p) m₀ a _ _ _ ds hd hc
  · intro a
    simpa only [endpointVertex_self] using endpoint_path_defect w b (transverse b p) m₀ a _ _ _ es he hce

end GammaFPP.CrossingBridge

end OAI
