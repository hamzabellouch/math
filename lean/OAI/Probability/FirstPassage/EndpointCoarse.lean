import OAI.Probability.FirstPassage.EndpointExtensions

namespace OAI

namespace PlanarFPP
open Set

lemma endpoint_coarse_columns (A : ℝ) (m J : ℕ) (x : ℤ)
    (hx : |(x : ℝ)| ≤ A*(2 : ℝ)^m) :
    |(entranceColumn x m J : ℝ)| ≤ (A+2)*(2 : ℝ)^m ∧
      |(exitColumn x m J : ℝ)| ≤ (A+2)*(2 : ℝ)^m := by
  have hl := entranceColumn_span x m J
  have hr := exitColumn_span x m J
  have hl' : (gridMesh m J : ℝ) ≤ (x : ℝ)-(entranceColumn x m J : ℝ) ∧
      (x : ℝ)-(entranceColumn x m J : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast hl
  have hr' : (gridMesh m J : ℝ) ≤ (exitColumn x m J : ℝ)-(x : ℝ) ∧
      (exitColumn x m J : ℝ)-(x : ℝ) < 2*(gridMesh m J : ℝ) := by exact_mod_cast hr
  have hd := gridMesh_le_scale m J
  have hd0 : (0 : ℝ) < gridMesh m J := by exact_mod_cast gridMesh_pos m J
  have hx' := abs_le.mp hx
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hl'.1,hl'.2,hr'.1,hr'.2]

lemma endpointBox_mono (b A A' R R' : ℝ) (k m : ℕ) (hA : A ≤ A') (hR : R ≤ R') :
    endpointBox b A R k m ⊆ endpointBox b A' R' k m := by
  intro p hp
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_right hA (by positivity)),
    hp.2.trans (mul_le_mul_of_nonneg_right hR (by positivity))⟩

theorem gridConnections_extend_negative_path (w : Edge → ℝ) (b m₀ K A R a ε : ℝ)
    (hK : 0 ≤ K) (hm : 0 < m₀) (hR : 0 ≤ R) (hε : 0 < ε)
    (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m) (hlast : gridLastLevel m ≤ k)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (herror : 2*endpointExtensionError K k J+2*|a| ≤ ε*(2 : ℝ)^k/2)
    (hscale : (2*R*|a| /m₀)*(2 : ℝ)^k ≤ (gridMesh m J : ℝ))
    (p : Vertex) (ds : List Step) (hin : PathIn p ds (endpointBox b A R k m))
    (hcost : defect w b m₀ a p ds < -ε*(2 : ℝ)^k) :
    ∃ X Y : ℤ, gridMesh m J ∣ X ∧ gridMesh m J ∣ Y ∧
      |(X : ℝ)| ≤ (A+2)*(2 : ℝ)^m ∧ |(Y : ℝ)| ≤ (A+2)*(2 : ℝ)^m ∧
      (gridMesh m J : ℝ) ≤ ((Y-X : ℤ) : ℝ) ∧
      ∃ q es, q.1=X ∧ (q+displacement es).1=Y ∧
        PathIn q es (endpointBox b (A+4) (R+2*(K+200)) k m) ∧
        defect w b m₀ a q es < -(ε/2)*(2 : ℝ)^k := by
  let z := p+displacement ds
  have hp : p ∈ endpointBox b A R k m := by simpa using hin 0 (by omega)
  have hz : z ∈ endpointBox b A R k m := by simpa [z] using hin ds.length le_rfl
  obtain ⟨l,_unused,hl,_hu,hld,_hud,hil,_hiu⟩ :=
    gridConnections_endpoint_defects w b m₀ K A R hK k m J hJ hJlast hlast hg p hp
  obtain ⟨_unused',u,_hl,hu,_hld,hud,_hil,hiu⟩ :=
    gridConnections_endpoint_defects w b m₀ K A R hK k m J hJ hJlast hlast hg z hz
  let q := endpointVertex b (transverse b p) (entranceColumn p.1 m J)
  have hrev := negative_defect_reverse_span w hg.1 b m₀ a R ((2 : ℝ)^k) ε hm hR
    (by positivity) hε.le p z ds rfl hp.2 hz.2 hcost
  have hspan := extended_columns_span p.1 z.1 m J (2*R*|a| /m₀) ((2 : ℝ)^k)
    (by convert hrev using 1; ring) hscale
  refine ⟨entranceColumn p.1 m J,exitColumn z.1 m J,entranceColumn_dvd _ _ _,exitColumn_dvd _ _ _,
    (endpoint_coarse_columns A m J p.1 hp.1).1,(endpoint_coarse_columns A m J z.1 hz.1).2,
    hspan,q,l++ds++u,rfl,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc]
    change ((endpointVertex b (transverse b p) (entranceColumn p.1 m J)+displacement l+
      displacement ds)+displacement u).1=exitColumn z.1 m J
    rw [hl]
    change (z+displacement u).1=exitColumn z.1 m J
    rw [hu]
    rfl
  · have him : PathIn p ds (endpointBox b (A+4) (R+2*(K+200)) k m) := by
      intro i hi
      exact endpointBox_mono b A (A+4) R (R+2*(K+200)) k m (by linarith) (by linarith) (hin i hi)
    apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hil (by simpa [hl] using him))
    simpa only [displacement_append,← add_assoc,hl] using hiu
  · rw [defect_append,defect_append]
    have he : q+displacement l=p := hl
    have he' : q+displacement (l++ds)=z := by rw [displacement_append,← add_assoc,he]
    rw [he,he']
    have hb := hld a
    have hc := hud a
    change defect w b m₀ a q l ≤ _ at hb
    linarith

end PlanarFPP

end OAI
