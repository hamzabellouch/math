import OAI.Probability.FirstPassage.EndpointConnection

namespace OAI

namespace PlanarFPP
open Set Finset

theorem gridConnections_exit_levels (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (x : ℤ) (hlo : -(A+4)*(2 : ℝ)^m ≤ (x : ℝ))
    (hhi : (exitColumn x m J : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) (n : ℕ) (hn : J+n ≤ gridLastLevel m) :
    ColumnConnection w b r m₀
      (∑ i ∈ range (n+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)))
      (endpointTube b r H (x-gridMesh m J) (exitColumn x m J+gridMesh m J))
      (-endpointColumn (-x) m (J+n)) (exitColumn x m J) := by
  let T := exitColumn x m J
  let d := gridMesh m J
  have hfloor (j : ℕ) : x ≤ -endpointColumn (-x) m j := by
    have h := (meshFloor_bounds (-x) (gridMesh m j) (gridMesh_pos m j)).1
    change meshFloor (-x) (gridMesh m j) ≤ -x at h
    dsimp [endpointColumn]
    omega
  have hT (j : ℕ) (hj : J ≤ j) : -endpointColumn (-x) m j ≤ T := by
    have hm := endpointColumn_mono (-x) m hj
    have hd := gridMesh_pos m J
    dsimp [T,exitColumn,entranceColumn]
    omega
  induction n with
  | zero =>
    have hdiv : gridMesh m J ∣ -endpointColumn (-x) m J := dvd_neg.mpr (meshFloor_dvd (-x) _)
    have hb := gridConnections_block_connection w b m₀ K A R H hK hH k m J hJ hg J
      ⟨le_refl _,by simpa using hn⟩ (herr J le_rfl (by simpa using hn))
      (-endpointColumn (-x) m J) T (x-d) (T+d) hdiv 1 (by omega)
      (by simp [T,exitColumn,entranceColumn]; ring)
      (hlo.trans (by exact_mod_cast hfloor J)) hhi
      (by dsimp [d]; have hh := hfloor J; omega) (by rfl) r hr
    simpa [T,d] using hb
  | succ n ih =>
    have hn' : J+n ≤ gridLastLevel m := by omega
    have hj : J ≤ J+n+1 := by omega
    have hjlast : J+n+1 ≤ gridLastLevel m := by omega
    have hp := ih hn'
    obtain ⟨N,hN,hstep⟩ := endpointColumn_step (-x) m (J+n)
    have hdiv : gridMesh m (J+n+1) ∣ -endpointColumn (-x) m (J+n+1) :=
      dvd_neg.mpr (meshFloor_dvd (-x) _)
    have hdm : gridMesh m (J+n+1) ≤ d := gridMesh_antitone m hj
    have hbefore := hT (J+n) (by omega)
    have hstart := hfloor (J+n+1)
    have hb := gridConnections_block_connection w b m₀ K A R H hK hH k m J hJ hg (J+n+1)
      ⟨hj,hjlast⟩ (herr _ hj hjlast) (-endpointColumn (-x) m (J+n+1))
      (-endpointColumn (-x) m (J+n)) (x-d) (T+d) hdiv N (by omega) (by omega)
      (hlo.trans (by exact_mod_cast hstart))
      ((by exact_mod_cast hbefore : ((-endpointColumn (-x) m (J+n) : ℤ) : ℝ) ≤ (T : ℝ)).trans hhi) (by omega) (by omega) r hr
    have hc := hb.trans hp
    rw [add_comm (16*((K+200)*((J+n+1 : ℕ) : ℝ)^2*gridWidth k (J+n+1)))] at hc
    simpa only [sum_range_succ,Nat.add_assoc] using hc

theorem gridConnections_exit (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J) (hlast : J ≤ gridLastLevel m)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herr : ∀ j, J ≤ j → j ≤ gridLastLevel m → (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (p : Vertex) (hlo : -(A+4)*(2 : ℝ)^m ≤ (p.1 : ℝ))
    (hhi : (exitColumn p.1 m J : ℝ) ≤ (A+4)*(2 : ℝ)^m) (hr : |transverse b p| ≤ R*(2 : ℝ)^k) :
    ∃ ds, p+displacement ds=endpointVertex b (transverse b p) (exitColumn p.1 m J) ∧
      pathCost w p ds ≤ m₀*((exitColumn p.1 m J-p.1 : ℤ) : ℝ)+
        ∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)) ∧
      PathIn p ds (endpointTube b (transverse b p) H (p.1-gridMesh m J) (exitColumn p.1 m J+gridMesh m J)) := by
  have hc := gridConnections_exit_levels w b m₀ K A R H hK hH k m J hJ hg herr
    p.1 hlo hhi (transverse b p) hr (gridLastLevel m-J) (by omega)
  rw [Nat.add_sub_of_le hlast,endpointColumn_last,neg_neg] at hc
  simpa only [ColumnConnection,endpointVertex_self] using hc

end PlanarFPP

end OAI
