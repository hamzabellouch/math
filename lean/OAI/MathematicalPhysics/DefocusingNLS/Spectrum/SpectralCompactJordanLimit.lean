import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactChainLimit

namespace OAI

/-! A sequence of normalized first chains would yield a first chain for
the limiting compact pencil. -/

open Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_pencil_no_jordan_sequence
    (K D : ℕ → E →L[ℂ] E) (K₀ D₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (hD : Tendsto D atTop (𝓝 D₀)) (L : E →L[ℂ] ℂ)
    (c : ℝ) (hpos : 0 < c)
    (hbase : ∀ u : E, L u=0 → c * ‖u‖ ≤ ‖u-K₀ u‖)
    (hclose : ∀ n, ‖K n-K₀‖ ≤ c/2)
    (u v : ℕ → E) (u₀ : E) (hlim : Tendsto u atTop (𝓝 u₀))
    (hu : ∀ n, K n (u n)=u n) (hnorm : ∀ n, L (u n)=1)
    (hchain : ∀ n, v n-K n (v n)=D n (u n))
    (hno : ∀ w : E, w-K₀ w ≠ D₀ u₀) : False := by
  let w := fun n => v n-L (v n) • u n
  have hwL (n : ℕ) : L (w n)=0 := by
    simp only [w,map_sub,map_smul,hnorm,smul_eq_mul,mul_one,sub_self]
  have hw (n : ℕ) : w n-K n (w n)=D n (u n) := by
    calc
      w n-K n (w n) = v n-K n (v n) := by
        simp only [w,map_sub,map_smul,hu]
        abel
      _ = D n (u n) := hchain n
  have hf : Tendsto (fun n => w n-K n (w n)) atTop (𝓝 (D₀ u₀)) := by
    simp only [hw]
    exact (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := E) (F := E)).continuous.continuousAt.tendsto.comp
      (hD.prodMk_nhds hlim)
  obtain ⟨w₀,_,he⟩ := compact_complement_forced_limit K K₀ hK hc L c hpos hbase hclose w hwL (D₀ u₀) hf
  exact hno w₀ he

end DefocusingNLS

end OAI
