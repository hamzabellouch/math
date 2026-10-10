import OAI.Probability.FirstPassage.ConnectorGeometry

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

def contactSign (plus : Bool) : ℝ := if plus then 1 else -1

@[simp] theorem abs_contactSign (plus : Bool) : |contactSign plus|=1 := by
  cases plus <;> norm_num [contactSign]

theorem contactSide_of_sign (plus : Bool) (r : ℝ) (hr : 0 < contactSign plus*r) :
    r ∈ contactSide plus := by
  cases plus <;> simpa [contactSign,contactSide] using hr

theorem trialWindow_scale_bounds (M : ℕ) (hM : 0 < M) (R s : ℝ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    s ≤ trialWindow M R s ∧ trialWindow M R s ≤ (200*M*(R+1))*s := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := Nat.le_ceil s
  have hc' := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
  have hbase : s ≤ (R+1)*(⌈s⌉₊ : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hM' (by positivity : 0 ≤ (R+1)*(⌈s⌉₊ : ℝ))
  have hupper := mul_le_mul_of_nonneg_left (show (⌈s⌉₊ : ℝ) ≤ 2*s by linarith)
    (show 0 ≤ 100*(M : ℝ)*(R+1) by positivity)
  unfold trialWindow trialSpacing
  constructor <;> nlinarith

noncomputable def sourceSupportCost (μ : Plane → ℝ) (b : ℝ) (plus : Bool)
    (ε s : ℝ) (p q : Vertex) : ℝ :=
  μ (direction b)*xCoord (latticeEmbed (q-p))+
    extremeSlope μ b plus*rCoord b (latticeEmbed (q-p))+ε*s/2

theorem exponential_source_connector_test {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ X : ℤ, ∀ Y a : ℝ, 1 ≤ a → a ≤ 2 →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent
        (connectorVertices b X ⌈D0*s⌉ Y (trialWindow M R s) s)
        (connectorWindow b X Y (trialWindow M R s))
        (connectorWindow b (X+⌈D0*s⌉)
          (Y+contactSign plus*a*trialWindow M R s) (trialWindow M R s))
        (sourceSupportCost μ b plus ε s)} < κ := by
  let C : ℝ := 200*M*(R+1)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨D0,hD0,hgap⟩ := connector_support_gap μ hμ b plus ε C hε hC
  let D := 2*(D0+1)+9*C/2
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D0,hD0,?_⟩
  intro κ hκ
  filter_upwards [exponential_allPairsRegionEvent h μ hμ ht D (ε/4) (1/2)
    hD (by positivity) (by norm_num) κ hκ,eventually_ge_atTop (1 : ℝ)] with s hs hs1
  intro X Y a ha₀ ha₁
  let S := trialWindow M R s
  let d : ℤ := ⌈D0*s⌉
  have hs0 : 0 < s := by linarith
  have hSb := trialWindow_scale_bounds M hM R s hR hs1
  have hS : s ≤ S := hSb.1
  have hSC : S ≤ C*s := hSb.2
  have hS0 : 0 < S := hs0.trans_le hS
  have hdlo : D0*s ≤ (d : ℝ) := Int.le_ceil _
  have hdhi : (d : ℝ) ≤ (D0+1)*s := by
    have hh : (d : ℝ) < D0*s+1 := Int.ceil_lt_add_one _
    nlinarith
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) ≤ d := by nlinarith
    exact_mod_cast this
  apply hs
  · intro p hp q hq
    exact (connector_union_diameter b hb X d Y S (contactSign plus) a hd0 hS0.le
      (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq).trans (by dsimp [D]; nlinarith)
  · intro p hp q hq
    have hx : xCoord (latticeEmbed (q-p))=(d : ℝ) := by
      change ((q-p).1 : ℝ)=_
      rw [Prod.fst_sub,hp.1,hq.1]
      congr 1
      omega
    have hr : rCoord b (latticeEmbed (q-p))=transverse b q-transverse b p := by
      simp [rCoord_apply,latticeEmbed,transverse]; ring
    have htrans := connector_transverse_displacement b X d Y S (contactSign plus) a
      hS0.le (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq
    have hpos : 0 < contactSign plus*rCoord b (latticeEmbed (q-p)) := by
      rw [hr]; linarith [htrans.1]
    have habs : |rCoord b (latticeEmbed (q-p))| ≤ 3*C*s := by
      have he : |rCoord b (latticeEmbed (q-p))| =
          contactSign plus*rCoord b (latticeEmbed (q-p)) := by
        calc
          _ = |contactSign plus*rCoord b (latticeEmbed (q-p))| := by simp [abs_mul]
          _ = _ := abs_of_pos hpos
      rw [he,hr]
      nlinarith [htrans.2]
    have hg := hgap s hs0 (latticeEmbed (q-p)) (by rw [hx]; exact hdlo)
      (contactSide_of_sign plus _ hpos) habs
    unfold sourceSupportCost
    linarith
  · intro p hp q hq
    simpa only [one_div,mul_comm (2⁻¹ : ℝ) s,← div_eq_mul_inv] using
      connector_tube_containment b hb X d Y S s (contactSign plus) a hd0 hs0.le hS
        (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq

end PlanarFPP

end OAI
