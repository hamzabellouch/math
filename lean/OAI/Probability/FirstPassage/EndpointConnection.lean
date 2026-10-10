import OAI.Probability.FirstPassage.EndpointBlocks

namespace OAI

namespace PlanarFPP
open Set

def ColumnConnection (w : Edge → ℝ) (b r m₀ E : ℝ) (S : Set Vertex) (X Y : ℤ) : Prop :=
  ∃ ds, endpointVertex b r X+displacement ds=endpointVertex b r Y ∧
    pathCost w (endpointVertex b r X) ds ≤ m₀*((Y-X : ℤ) : ℝ)+E ∧
    PathIn (endpointVertex b r X) ds S

lemma ColumnConnection.mono {w : Edge → ℝ} {b r m₀ E F : ℝ} {S T : Set Vertex} {X Y : ℤ}
    (h : ColumnConnection w b r m₀ E S X Y) (hE : E ≤ F) (hS : S ⊆ T) :
    ColumnConnection w b r m₀ F T X Y := by
  obtain ⟨ds,hd,hc,hin⟩ := h
  exact ⟨ds,hd,by linarith,fun i hi => hS (hin i hi)⟩

lemma ColumnConnection.trans {w : Edge → ℝ} {b r m₀ E F : ℝ} {S : Set Vertex} {X Y Z : ℤ}
    (h : ColumnConnection w b r m₀ E S X Y) (g : ColumnConnection w b r m₀ F S Y Z) :
    ColumnConnection w b r m₀ (E+F) S X Z := by
  obtain ⟨ds,hd,hc,hin⟩ := h
  obtain ⟨es,he,hce,hine⟩ := g
  refine ⟨ds++es,?_,?_,?_⟩
  · rw [displacement_append,← add_assoc,hd,he]
  · rw [pathCost_append,hd]
    push_cast at hc hce ⊢
    linarith
  · exact pathIn_append _ _ _ _ hin (by simpa [hd] using hine)

noncomputable def endpointTube (b r H : ℝ) (B T : ℤ) : Set Vertex :=
  {z | B ≤ z.1 ∧ z.1 ≤ T ∧ |transverse b z-r| ≤ H}

lemma gridConnections_block_connection (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m)
    (he : (K+200)*(j : ℝ)^2*gridWidth k j ≤ H)
    (X Y B T : ℤ) (hX : gridMesh m j ∣ X) (n : ℕ) (hn : n ≤ 16)
    (hXY : X+(n : ℤ)*gridMesh m j=Y)
    (hlo : -(A+4)*(2 : ℝ)^m ≤ (X : ℝ))
    (hhi : (Y : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (hB : B ≤ X-gridMesh m j) (hT : Y+gridMesh m j ≤ T)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) :
    ColumnConnection w b r m₀ (16*((K+200)*(j : ℝ)^2*gridWidth k j))
      (endpointTube b r H B T) X Y := by
  obtain ⟨ds,hd,hc,hin⟩ := gridConnections_block w b m₀ K A R H hK hH k m J hJ hg j hj he
    X hX n hlo (by simpa [hXY] using hhi) r hr
  have hn' : (n : ℝ) ≤ 16 := by exact_mod_cast hn
  have herr : (n : ℝ)*((K+200)*(j : ℝ)^2*gridWidth k j) ≤
      16*((K+200)*(j : ℝ)^2*gridWidth k j) := by
    apply mul_le_mul_of_nonneg_right hn'
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by exact_mod_cast (gridWidth_pos k j).le)
  refine ⟨ds,by simpa [hXY] using hd,?_,?_⟩
  · have heq : (n : ℤ)*gridMesh m j=Y-X := by omega
    rw [heq] at hc
    linarith
  · intro i hi
    have hz := hin i hi
    rw [hXY] at hz
    exact ⟨hB.trans hz.1,hz.2.1.trans hT,hz.2.2⟩

end PlanarFPP

end OAI
