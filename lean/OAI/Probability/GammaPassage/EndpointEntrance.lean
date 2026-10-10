import OAI.Probability.GammaPassage.EndpointConnection

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set Finset

/-- Complete greedy entrance through level J+n. At n=j*-J its endpoint is
exactly x, and each level is charged at most sixteen times. -/
theorem gridConnections_entrance_levels (w : Edge → ℝ) (shape rate b m₀ K A R H : ℝ)
    (hs : 0 < shape) (hrate : 0 < rate) (hK : 100 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent shape rate b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (Grid.attachmentAllowance shape rate K)*(j : ℝ)^2*gridWidth k j ≤ H)
    (x : ℤ) (hlo : -(A+4)*(2 : ℝ)^m ≤ (entranceColumn x m J : ℝ))
    (hhi : (x : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) (n : ℕ) (hn : J+n ≤ gridLastLevel m) :
    ColumnConnection w b r m₀
      (∑ i ∈ range (n+1),16*((Grid.attachmentAllowance shape rate K)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
      (endpointTube b r H (entranceColumn x m J-gridMesh m J) (x+gridMesh m J))
      (entranceColumn x m J) (endpointColumn x m (J+n)) := by
  let B := entranceColumn x m J
  let d := gridMesh m J
  have hfloor (j : ℕ) : endpointColumn x m j ≤ x :=
    (meshFloor_bounds x _ (gridMesh_pos m j)).1
  have hfloorR (j : ℕ) : (endpointColumn x m j : ℝ) ≤ (x : ℝ) := by exact_mod_cast hfloor j
  have hB (j : ℕ) (hj : J ≤ j) : B ≤ endpointColumn x m j := by
    have hm := endpointColumn_mono x m hj
    have hd := gridMesh_pos m J
    dsimp [B,entranceColumn]
    omega
  induction n with
  | zero =>
    have hb := gridConnections_block_connection w shape rate b m₀ K A R H hs hrate hK hH k m J hJ hg J
      ⟨le_refl _,by simpa using hn⟩ (herr J le_rfl (by simpa using hn)) B
      (endpointColumn x m J) (B-d) (x+d) (entranceColumn_dvd x m J) 1 (by omega)
      (by simp [B,entranceColumn]) hlo
      ((hfloorR J).trans hhi) (by rfl) (by dsimp [d]; have hh := hfloor J; omega) r hr
    simpa [B,d] using hb
  | succ n ih =>
    have hn' : J+n ≤ gridLastLevel m := by omega
    have hj : J ≤ J+n+1 := by omega
    have hjlast : J+n+1 ≤ gridLastLevel m := by omega
    have hp := ih hn'
    obtain ⟨N,hN,hstep⟩ := endpointColumn_step x m (J+n)
    have hdiv : gridMesh m (J+n+1) ∣ endpointColumn x m (J+n) :=
      dvd_trans (gridMesh_divides m (J+n)) (meshFloor_dvd x _)
    have hdm : gridMesh m (J+n+1) ≤ d := gridMesh_antitone m hj
    have hbefore := hB (J+n) (by omega)
    have hb := gridConnections_block_connection w shape rate b m₀ K A R H hs hrate hK hH k m J hJ hg (J+n+1)
      ⟨hj,hjlast⟩ (herr _ hj hjlast) (endpointColumn x m (J+n))
      (endpointColumn x m (J+n+1)) (B-d) (x+d) hdiv N (by omega) hstep
      (hlo.trans (by exact_mod_cast hbefore))
      ((hfloorR (J+n+1)).trans hhi)
      (by omega) (by have hh := hfloor (J+n+1); omega) r hr
    have hc := hp.trans hb
    simpa only [sum_range_succ,Nat.add_assoc] using hc

/-- Entrance path obtained by greedy mesh subdivision. -/
theorem gridConnections_entrance (w : Edge → ℝ) (shape rate b m₀ K A R H : ℝ)
    (hs : 0 < shape) (hrate : 0 < rate) (hK : 100 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J) (hlast : J ≤ gridLastLevel m)
    (hg : w ∈ gridConnectionsEvent shape rate b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (Grid.attachmentAllowance shape rate K)*(j : ℝ)^2*gridWidth k j ≤ H)
    (p : Vertex) (hlo : -(A+4)*(2 : ℝ)^m ≤ (entranceColumn p.1 m J : ℝ))
    (hhi : (p.1 : ℝ) ≤ (A+4)*(2 : ℝ)^m) (hr : |transverse b p| ≤ R*(2 : ℝ)^k) :
    ∃ ds, endpointVertex b (transverse b p) (entranceColumn p.1 m J)+displacement ds=p ∧
      pathCost w (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds ≤
        m₀*((p.1-entranceColumn p.1 m J : ℤ) : ℝ)+
        ∑ i ∈ range (gridLastLevel m-J+1),16*((Grid.attachmentAllowance shape rate K)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)) ∧
      PathIn (endpointVertex b (transverse b p) (entranceColumn p.1 m J)) ds
        (endpointTube b (transverse b p) H (entranceColumn p.1 m J-gridMesh m J) (p.1+gridMesh m J)) := by
  have hc := gridConnections_entrance_levels w shape rate b m₀ K A R H hs hrate hK hH k m J hJ hg herr
    p.1 hlo hhi (transverse b p) hr (gridLastLevel m-J) (by omega)
  rw [Nat.add_sub_of_le hlast,endpointColumn_last] at hc
  simpa only [ColumnConnection,endpointVertex_self] using hc

end GammaFPP.CrossingBridge

end OAI
