import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.FineChartGraph

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology

theorem curved_holonomy_local_bound {S : Set ℝ} {G : ℝ → ℝ → ℝ} {u H : ℝ → ℝ}
    {κ ℓ K : ℝ} (hκ : 0≤κ) (hℓ : 0≤ℓ) (hK : 0≤K) (hcone : κ*ℓ<1)
    (hG : ∀ a∈S,∀ s t, |G a s-G a t|≤κ*|s-t|)
    (hu : ∀ s t,|u s-u t|≤ℓ*|s-t|)
    (hholo : ∀ x a,a∈S → ∀ᶠ b in 𝓝[S] a,|G b x-G a x|≤K*|b-a|)
    (hmatch : ∀ a∈S,H a=G a (u (H a))) :
    ∀ a∈S,∀ᶠ b in 𝓝[S] a,|H b-H a|≤(K/(1-κ*ℓ))*|b-a| := by
  intro a ha
  filter_upwards [hholo (u (H a)) a ha,self_mem_nhdsWithin] with b hb hbS
  by_cases he : H b=H a
  · rw [he,sub_self,abs_zero]
    exact mul_nonneg (div_nonneg hK (sub_pos.mpr hcone).le) (abs_nonneg _)
  have hm : |H b-H a|≤κ*ℓ*|H b-H a|+K*|b-a| := by
    calc
      |H b-H a| = |G b (u (H b))-G a (u (H a))| := by rw [←hmatch b hbS,←hmatch a ha]
      _ ≤ |G b (u (H b))-G b (u (H a))|+|G b (u (H a))-G a (u (H a))| := abs_sub_le _ _ _
      _ ≤ κ*(ℓ*|H b-H a|)+K*|b-a| := add_le_add ((hG b hbS _ _).trans (by
        simpa only [mul_comm] using mul_le_mul (hu _ _) le_rfl hκ (mul_nonneg hℓ (abs_nonneg _)))) hb
      _ = κ*ℓ*|H b-H a|+K*|b-a| := by ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hcone)).mpr
  nlinarith

theorem curved_inverse_holonomy_local_bound {S T : Set ℝ} {G : ℝ → ℝ → ℝ} {u J : ℝ → ℝ}
    {κ ℓ K : ℝ} (hκ : 0≤κ) (hℓ : 0≤ℓ) (hK : 0≤K)
    (hG : ∀ a∈S,∀ s t, |G a s-G a t|≤κ*|s-t|)
    (hu : ∀ s t,|u s-u t|≤ℓ*|s-t|)
    (hholo : ∀ x a,a∈S → ∀ᶠ b in 𝓝[S] a,|b-a|≤K*|G b x-G a x|)
    (hJ : ContinuousOn J T) (hJS : MapsTo J T S)
    (hmatch : ∀ t∈T,t=G (J t) (u t)) :
    ∀ a∈T,∀ᶠ b in 𝓝[T] a,|J b-J a|≤(K*(1+κ*ℓ))*|b-a| := by
  intro a ha
  have ht : Tendsto J (𝓝[T] a) (𝓝[S] (J a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hJ a ha,Eventually.mono self_mem_nhdsWithin hJS⟩
  filter_upwards [ht.eventually (hholo (u a) (J a) (hJS ha)),self_mem_nhdsWithin] with b hb hbT
  have hm : |G (J b) (u a)-G (J a) (u a)|≤(1+κ*ℓ)*|b-a| := by
    calc
      |G (J b) (u a)-G (J a) (u a)| = |G (J b) (u a)-a| := by rw [←hmatch a ha]
      _ ≤ |G (J b) (u a)-G (J b) (u b)|+|G (J b) (u b)-a| := abs_sub_le _ _ _
      _ ≤ κ*(ℓ*|a-b|)+|b-a| := add_le_add
        ((hG (J b) (hJS hbT) _ _).trans (by
          simpa only [mul_comm] using mul_le_mul (hu _ _) le_rfl hκ (mul_nonneg hℓ (abs_nonneg _)))) (by rw [←hmatch b hbT])
      _ = (1+κ*ℓ)*|b-a| := by rw [abs_sub_comm a b]; ring
  exact hb.trans ((mul_le_mul_of_nonneg_left hm hK).trans_eq (by ring))

theorem curved_holonomy_null_image {S : Set ℝ} {G : ℝ → ℝ → ℝ} {u H : ℝ → ℝ}
    {κ ℓ K : ℝ} (hκ : 0≤κ) (hℓ : 0≤ℓ) (hK : 0≤K) (hcone : κ*ℓ<1)
    (hG : ∀ a∈S,∀ s t, |G a s-G a t|≤κ*|s-t|)
    (hu : ∀ s t,|u s-u t|≤ℓ*|s-t|)
    (hholo : ∀ x a,a∈S → ∀ᶠ b in 𝓝[S] a,|G b x-G a x|≤K*|b-a|)
    (hmatch : ∀ a∈S,H a=G a (u (H a)))
    {Z : Set ℝ} (hZS : Z⊆S) (hZ : volume Z=0) : volume (H '' Z)=0 :=
  null_image_of_pointwise_local_bound (div_nonneg hK (sub_pos.mpr hcone).le)
    (curved_holonomy_local_bound hκ hℓ hK hcone hG hu hholo hmatch) hZS hZ

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

def AffineGraphControl {X : Type*} (G : X → ℝ → ℝ) (I : Set ℝ) (K : ℝ) : Prop :=
  ∀ c∈I,∀ d∈I,∃ H : ℝ → ℝ,
    ContinuousOn H (range (fun a => G a c)) ∧ (∀ a,H (G a c)=G a d) ∧
    ∀ z∈range (fun a => G a c),∀ᶠ z' in 𝓝[range (fun a => G a c)] z,|H z'-H z|≤K*|z'-z|

lemma AffineGraphControl.fibres {X : Type*} {G : X → ℝ → ℝ} {I : Set ℝ} {K : ℝ}
    (h : AffineGraphControl G I K) {c d : ℝ} (hc : c∈I) (hd : d∈I) (a b : X) :
    G a c=G b c ↔ G a d=G b d := by
  obtain ⟨H,_,hH,_⟩ := h c hc d hd
  obtain ⟨J,_,hJ,_⟩ := h d hd c hc
  constructor
  · intro he; rw [←hH a,←hH b,he]
  · intro he; rw [←hJ a,←hJ b,he]

theorem compact_curved_inverse_control {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {G : X → ℝ → ℝ} (hGc : Continuous (fun p : X×ℝ => G p.1 p.2))
    {I : Set ℝ} {K κ ℓ : ℝ} (hK : 0≤K) (hκ : 0≤κ) (hℓ : 0≤ℓ) (hcone : κ*ℓ<1)
    (hG : ∀ a s t,|G a s-G a t|≤κ*|s-t|) (hh : AffineGraphControl G I K)
    (u : ℝ → ℝ) (hu : ∀ s t,|u s-u t|≤ℓ*|s-t|)
    (g : X → ℝ) (hg : Continuous g) (hmatch : ∀ a,g a=G a (u (g a)))
    (hwithin : ∀ a,u (g a)∈I)
    {c : ℝ} (hc : c∈I) :
    ∃ J : ℝ → ℝ,ContinuousOn J (range g) ∧ (∀ a,J (g a)=G a c) ∧
      ∀ t∈range g,∀ᶠ t' in 𝓝[range g] t,|J t'-J t|≤(K*(1+κ*ℓ))*|t'-t| := by
  have fibre (a b : X) (d : ℝ) (hd : d∈I) : g a=g b ↔ G a d=G b d := by
    constructor
    · intro he
      apply (hh.fibres (hwithin a) hd a b).mp
      rw [←hmatch a,he,←he,he,←hmatch b]
    · intro he
      have hsame := (hh.fibres (hwithin b) hd a b).mpr he
      have hdist : |g a-g b|≤κ*(ℓ*|g a-g b|) := by
        calc
          |g a-g b| = |G a (u (g a))-G a (u (g b))| := by rw [hsame,←hmatch a,←hmatch b]
          _ ≤ κ*(ℓ*|g a-g b|) := (hG a _ _).trans (mul_le_mul_of_nonneg_left (hu _ _) hκ)
      apply sub_eq_zero.mp
      apply abs_eq_zero.mp
      exact le_antisymm (by nlinarith [mul_nonneg (sub_pos.mpr hcone).le (abs_nonneg (g a-g b))]) (abs_nonneg _)
  obtain ⟨J,hJ,hJval⟩ := compact_fibre_descent hg
    (hGc.comp (continuous_id.prodMk continuous_const)) (fun a b he => (fibre a b c hc).mp he)
  change ∀ a,J (g a)=G a c at hJval
  refine ⟨J,hJ,hJval,?_⟩
  rintro t ⟨a,rfl⟩
  let d := u (g a)
  have hd : d∈I := hwithin a
  obtain ⟨H,hH,hHval,hHbound⟩ := hh d hd c hc
  obtain ⟨V,hV,hVval⟩ := compact_fibre_descent hg
    (show Continuous (fun b => G b d) from hGc.comp (continuous_id.prodMk continuous_const)) (fun a b he => (fibre a b d hd).mp he)
  change ∀ b,V (g b)=G b d at hVval
  have hmaps : MapsTo V (range g) (range (fun b => G b d)) := by
    rintro _ ⟨b,rfl⟩; exact ⟨b,(hVval b).symm⟩
  have hv : Tendsto V (𝓝[range g] (g a)) (𝓝[range (fun b => G b d)] (G a d)) := by
    rw [←hVval a]
    exact tendsto_nhdsWithin_iff.mpr ⟨hV (g a) ⟨a,rfl⟩,Eventually.mono self_mem_nhdsWithin hmaps⟩
  filter_upwards [hv.eventually (hHbound (G a d) ⟨a,rfl⟩),self_mem_nhdsWithin] with t ht htS
  obtain ⟨b,rfl⟩ := htS
  rw [hVval b,hHval b,hHval a] at ht
  rw [hJval b,hJval a]
  apply ht.trans
  have hm : |G b d-G a d|≤(1+κ*ℓ)*|g b-g a| := by
    have hea : G a d=g a := (hmatch a).symm
    calc
      |G b d-G a d| = |G b (u (g a))-g a| := by rw [hea]
      _ ≤ |G b (u (g a))-G b (u (g b))|+|G b (u (g b))-g a| := abs_sub_le _ _ _
      _ ≤ κ*(ℓ*|g a-g b|)+|g b-g a| := add_le_add
        ((hG b _ _).trans (by
          simpa only [mul_comm] using mul_le_mul (hu _ _) le_rfl hκ (mul_nonneg hℓ (abs_nonneg _)))) (by rw [←hmatch b])
      _ = (1+κ*ℓ)*|g b-g a| := by rw [abs_sub_comm (g a) (g b)]; ring
  exact (mul_le_mul_of_nonneg_left hm hK).trans_eq (by ring)

end StandardMapEntropy

namespace StandardMapEntropy
open Set Filter Topology
open scoped Topology
lemma AffineGraphControl.comp {X Y : Type*} {G : Y → ℝ → ℝ} {I : Set ℝ} {K : ℝ}
    (h : AffineGraphControl G I K) (f : X → Y) : AffineGraphControl (fun a s => G (f a) s) I K := by
  intro c hc d hd
  obtain ⟨H,hH,hval,hb⟩ := h c hc d hd
  have hsub : range (fun a : X => G (f a) c)⊆range (fun a : Y => G a c) := by
    rintro _ ⟨a,rfl⟩; exact ⟨f a,rfl⟩
  exact ⟨H,hH.mono hsub,fun a => hval (f a),fun z hz => (hb z (hsub hz)).filter_mono (nhdsWithin_mono z hsub)⟩
end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma AffineGraphControl.scale {X : Type*} {G : X → ℝ → ℝ} {I J : Set ℝ} {K α β : ℝ}
    (h : AffineGraphControl G I K) (hβ : β≠0) (hJ : ∀ t∈J,t/α∈I) :
    AffineGraphControl (fun a s => β*G a (s/α)) J K := by
  intro c hc d hd
  obtain ⟨H,hH,hHval,hHbound⟩ := h (c/α) (hJ c hc) (d/α) (hJ d hd)
  let S := range (fun a => β*G a (c/α))
  have hmaps : MapsTo (fun t : ℝ => t/β) S (range (fun a => G a (c/α))) := by
    rintro _ ⟨a,rfl⟩
    exact ⟨a,(mul_div_cancel_left₀ _ hβ).symm⟩
  have hcont : ContinuousOn (fun t : ℝ => H (t/β)) S :=
    hH.comp (continuous_id.div_const β).continuousOn hmaps
  refine ⟨(fun t => β*H (t/β)),continuousOn_const.mul hcont,?_,?_⟩
  · intro a
    dsimp only
    rw [mul_div_cancel_left₀ _ hβ,hHval]
  · intro t ht
    have hv : Tendsto (fun t : ℝ => t/β) (𝓝[S] t) (𝓝[range (fun a => G a (c/α))] (t/β)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuous_id.div_const β).continuousAt.continuousWithinAt,
        Eventually.mono self_mem_nhdsWithin hmaps⟩
    filter_upwards [hv.eventually (hHbound (t/β) (hmaps ht))] with t' hh
    rw [←mul_sub,abs_mul]
    apply (mul_le_mul_of_nonneg_left hh (abs_nonneg β)).trans_eq
    rw [←sub_div,abs_div]
    field_simp

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)
noncomputable def holonomyConstant : ℝ := 2*Real.exp (8*B.δ/(1-(Real.exp (-χ+B.ε)+B.δ)))
lemma holonomyConstant_pos : 0<B.holonomyConstant := by unfold holonomyConstant; positivity
noncomputable def stableInterval : Set ℝ := Icc (-B.r/2) (B.r/2)
noncomputable def unstableInterval : Set ℝ := Icc (-|B.α| * B.r'/2) (|B.α| * B.r'/2)
lemma mem_stableInterval {s : ℝ} : s∈B.stableInterval ↔ |s|≤B.r/2 := by
  change -B.r/2 ≤ s ∧ s ≤ B.r/2 ↔ _
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
lemma mem_unstableInterval {s : ℝ} : s∈B.unstableInterval ↔ |s|≤|B.α| * B.r'/2 := by
  change -|B.α| * B.r'/2 ≤ s ∧ s ≤ |B.α| * B.r'/2 ↔ _
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
lemma reverseCoordinates_chart (p : RealPlane) : B.reverseCoordinates (B.chart p)=(p.2/B.α,p.1/B.β) := by
  have he := B.coordinates_swap (B.chart p)
  rw [B.coordinates_chart] at he
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change p.1=B.β*(B.reverseCoordinates (B.chart p)).2 at he1
  change p.2=B.α*(B.reverseCoordinates (B.chart p)).1 at he2
  apply Prod.ext
  · apply (eq_div_iff B.α_ne).mpr
    nlinarith [he2]
  · apply (eq_div_iff B.β_ne).mpr
    nlinarith [he1]
lemma reverse_chart_coordinates (v : ℂ) : tangentReversal B.centre+
    fineFrame k χ B.ε B.δ (complexProjection (tangentReversal B.centre)) (B.reverseCoordinates v)=tangentReversal v := by
  rw [reverseCoordinates,fineFrame_inverse k χ B.ε B.δ_pos _ B.reverse_regular]
  abel
end ReversibleRectangleBlock

namespace ReversibleGraphFamilies
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} (F : ReversibleGraphFamilies B)

lemma stable_control (hk : 0≤k) : AffineGraphControl F.G B.stableInterval B.holonomyConstant := by
  let _ : CompactSpace B.carrier := isCompact_iff_compactSpace.mp B.compact
  intro c hc d hd
  obtain ⟨H,J,hH,hJ,hval,_,_,hHb,_⟩ := actual_graph_holonomy_bounds k hk χ B.ε B.δ B.ε_pos.le
    B.δ_pos B.δ_small B.contraction B.slow B.centre B.centre_regular
    (fun a : B.carrier => (a : ℂ)) (fun a => B.regular a a.property) F.G F.stableParameter F.continuous_G
    B.r_pos B.r_small B.R_pos (fun a => B.radius a a.property) B.size
    (fun a => (B.frames a a.property).trans (by linarith [B.η_small]))
    (fun a => B.coframes a a.property) B.stableInterval
    (fun a s _ => F.stable_bound a s)
    (fun a s hs => F.stable_representation a s (B.mem_stableInterval.mp hs)) hc hd
  exact ⟨H,hH,fun a => (hval a).1,hHb⟩

lemma reverse_representation (a : B.carrier) {s : ℝ} (hs : |s|≤B.r'/2) :
    tangentReversal B.centre+fineFrame k χ B.ε B.δ (complexProjection (tangentReversal B.centre))
      (s,F.U a (B.α*s)/B.β)=
    fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction (tangentReversal a)
      (B.reversed a a.property) (F.unstableParameter a (B.α*s)) := by
  have has : |B.α*s|≤|B.α| * B.r'/2 := by rw [abs_mul]; nlinarith [abs_nonneg B.α]
  have he := F.unstable_representation a (B.α*s) has
  have hc := congrArg B.reverseCoordinates he
  rw [B.reverseCoordinates_chart] at hc
  have heα : B.α*s/B.α=s := mul_div_cancel_left₀ s B.α_ne
  rw [heα] at hc
  have hz := congrArg (fun p => tangentReversal B.centre+
    fineFrame k χ B.ε B.δ (complexProjection (tangentReversal B.centre)) p) hc
  rw [B.reverse_chart_coordinates] at hz
  simpa only [fineUnstableCurve,tangentReversal_involutive] using hz

lemma unstable_control (hk : 0≤k) : AffineGraphControl F.U B.unstableInterval B.holonomyConstant := by
  let _ : CompactSpace B.carrier := isCompact_iff_compactSpace.mp B.compact
  let GR (a : B.carrier) (s : ℝ) := F.U a (B.α*s)/B.β
  let σ (a : B.carrier) (s : ℝ) := F.unstableParameter a (B.α*s)
  let I : Set ℝ := Icc (-B.r'/2) (B.r'/2)
  have hGR : Continuous (fun p : B.carrier×ℝ => GR p.1 p.2) :=
    (F.continuous_U.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))).div_const B.β
  have hcontrol : AffineGraphControl GR I B.holonomyConstant := by
    intro c hc d hd
    obtain ⟨H,J,hH,hJ,hval,_,_,hHb,_⟩ := actual_graph_holonomy_bounds k hk χ B.ε B.δ B.ε_pos.le
      B.δ_pos B.δ_small B.contraction B.slow (tangentReversal B.centre) B.reverse_regular
      (fun a : B.carrier => tangentReversal a) (fun a => B.reversed a a.property) GR σ hGR
      B.r'_pos B.r'_small B.R'_pos (fun a => B.reverse_radius a a.property) B.reverse_size
      (fun a => (B.reverse_frames a a.property).trans (by linarith [B.η_small]))
      (fun a => B.reverse_coframes a a.property) I
      (fun a s _ => F.unstable_bound a (B.α*s))
      (fun a s hs => F.reverse_representation a (abs_le.mpr ⟨by linarith [hs.1],hs.2⟩)) hc hd
    exact ⟨H,hH,fun a => (hval a).1,hHb⟩
  have hscaled := hcontrol.scale (α := B.α) B.β_ne (J := B.unstableInterval) (by
    intro s hs
    have hs' := B.mem_unstableInterval.mp hs
    have hab : |s/B.α|≤B.r'/2 := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr B.α_ne)).mpr (by nlinarith)
    exact ⟨by linarith [(abs_le.mp hab).1],(abs_le.mp hab).2⟩)
  have he : (fun a s => B.β*GR a (s/B.α))=F.U := by
    funext a s
    dsimp only [GR]
    rw [mul_div_cancel₀ _ B.β_ne,mul_div_cancel₀ _ B.α_ne]
  rw [he] at hscaled
  exact hscaled

end ReversibleGraphFamilies
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

noncomputable def coordinateCarrier : Set RealPlane := B.coordinates '' B.carrier
lemma compact_coordinateCarrier : IsCompact B.coordinateCarrier := B.compact.image B.continuous_coordinates
noncomputable def label (p : B.coordinateCarrier) : B.carrier := ⟨B.chart p,by
  obtain ⟨v,hv,he⟩ := p.property
  change B.coordinates v=(p : RealPlane) at he
  rw [←he,B.chart_coordinates]
  exact hv⟩
lemma continuous_label : Continuous B.label :=
  (B.continuous_chart.comp continuous_subtype_val).subtype_mk _
@[simp] lemma coordinates_label (p : B.coordinateCarrier) : B.coordinates (B.label p)=(p : RealPlane) :=
  B.coordinates_chart p
lemma chart_image_carrier : B.chart '' B.coordinateCarrier=B.carrier := by
  ext v
  constructor
  · rintro ⟨p,⟨v',hv',hp⟩,rfl⟩
    rw [←hp,B.chart_coordinates]
    exact hv'
  · intro hv
    exact ⟨B.coordinates v,⟨v,hv,rfl⟩,B.chart_coordinates v⟩

lemma volume_chart_image {S : Set RealPlane} (hS : MeasurableSet S) :
    volume (B.chart '' S)=ENNReal.ofReal (fineVolumeFactor k χ B.ε B.δ (complexProjection B.centre))*volume S := by
  have he : B.chart '' S=(fun z : ℂ => B.centre+z) ''
      ((fineSize k χ B.ε B.δ (complexProjection B.centre) • lyapunovFrame k χ (complexProjection B.centre)) '' (pairToComplex '' S)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [he,Set.image_add_left,measure_preimage_add,Measure.addHaar_image_continuousLinearMap,volume_pairToComplex_image hS]
  rfl
lemma positive_coordinateCarrier : 0<volume B.coordinateCarrier := by
  by_contra h
  have hz : volume B.coordinateCarrier=0 := le_antisymm (not_lt.mp h) (bot_le)
  have hh := B.volume_chart_image B.compact_coordinateCarrier.measurableSet
  rw [B.chart_image_carrier,hz,mul_zero] at hh
  exact B.positive.ne' hh
lemma volume_coordinate_univ : (volume : Measure B.coordinateCarrier) univ=volume B.coordinateCarrier := by
  change (Measure.comap Subtype.val volume) univ=volume B.coordinateCarrier
  rw [comap_subtype_coe_apply B.compact_coordinateCarrier.measurableSet]
  simp only [Set.image_univ,Subtype.range_coe]
lemma finite_coordinate_volume : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := by
  apply (isFiniteMeasure_iff _).mpr
  rw [B.volume_coordinate_univ]
  exact B.compact_coordinateCarrier.measure_lt_top

lemma chart_quasiMeasurePreserving : QuasiMeasurePreserving B.chart volume volume := by
  let L : ℂ →L[ℝ] ℂ := fineSize k χ B.ε B.δ (complexProjection B.centre) • lyapunovFrame k χ (complexProjection B.centre)
  have hi : Function.Injective L := by
    intro z z' he
    have hh : fineFrame k χ B.ε B.δ (complexProjection B.centre) (complexToPair z)=
        fineFrame k χ B.ε B.δ (complexProjection B.centre) (complexToPair z') := by
      simpa only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,pairToComplex_complexToPair] using he
    have hh' := congrArg (fineInverse k χ B.ε B.δ (complexProjection B.centre)) hh
    rw [fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular,
      fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular] at hh'
    exact congrArg pairToComplex hh'
  have hdet : L.det≠0 := by
    intro hzero
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hi)
  have hp : MeasurePreserving pairToComplex volume volume := by
    exact Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  exact (measurePreserving_add_left volume B.centre).quasiMeasurePreserving.comp
    ((L.quasiMeasurePreserving volume hdet).comp hp.quasiMeasurePreserving)

end ReversibleRectangleBlock
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

theorem label_nonsingular_of_vertical_inverse {K : Set (ℝ×ℝ)} (hK : MeasurableSet K)
    (f : K → ℝ) (hf : Measurable f) {I : Set ℝ} (hwithin : ∀ a : K,(a : ℝ×ℝ).1∈I)
    (hinv : ∀ c∈I,∃ J : ℝ → ℝ,
      (∀ a : K,(a : ℝ×ℝ).1=c → J (f a)=(a : ℝ×ℝ).2) ∧
      ∀ Z : Set ℝ,Z⊆range f → volume Z=0 → volume (J '' Z)=0) :
    QuasiMeasurePreserving f (volume : Measure K) volume := by
  refine ⟨hf,AbsolutelyContinuous.mk fun N hN hNz => ?_⟩
  rw [map_apply hf hN]
  change Measure.comap Subtype.val volume (f ⁻¹' N)=0
  rw [comap_subtype_coe_apply hK]
  let S : Set (ℝ×ℝ) := Subtype.val '' (f ⁻¹' N)
  have hS : MeasurableSet S := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr (hN.preimage hf)
  change volume S=0
  rw [Measure.volume_eq_prod,Measure.prod_apply hS]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro c
  by_cases hc : c∈I
  · obtain ⟨J,hJ,hJnull⟩ := hinv c hc
    apply measure_mono_null (t := J '' (N∩range f)) _ (hJnull _ inter_subset_right (measure_mono_null inter_subset_left hNz))
    rintro t ⟨a,ha,he⟩
    have h1 : (a : ℝ×ℝ).1=c := congrArg Prod.fst he
    have h2 : (a : ℝ×ℝ).2=t := congrArg Prod.snd he
    exact ⟨f a,⟨ha,⟨a,rfl⟩⟩,(hJ a h1).trans h2⟩
  · apply measure_mono_null (t := ∅) _ (measure_empty)
    rintro t ⟨a,ha,he⟩
    have he' : (a : ℝ×ℝ).1=c := congrArg Prod.fst he
    exact (hc (he' ▸ hwithin a)).elim

theorem label_nonsingular_of_horizontal_inverse {K : Set (ℝ×ℝ)} (hK : MeasurableSet K)
    (f : K → ℝ) (hf : Measurable f) {I : Set ℝ} (hwithin : ∀ a : K,(a : ℝ×ℝ).2∈I)
    (hinv : ∀ c∈I,∃ J : ℝ → ℝ,
      (∀ a : K,(a : ℝ×ℝ).2=c → J (f a)=(a : ℝ×ℝ).1) ∧
      ∀ Z : Set ℝ,Z⊆range f → volume Z=0 → volume (J '' Z)=0) :
    QuasiMeasurePreserving f (volume : Measure K) volume := by
  refine ⟨hf,AbsolutelyContinuous.mk fun N hN hNz => ?_⟩
  rw [map_apply hf hN]
  change Measure.comap Subtype.val volume (f ⁻¹' N)=0
  rw [comap_subtype_coe_apply hK]
  let S : Set (ℝ×ℝ) := Subtype.val '' (f ⁻¹' N)
  have hS : MeasurableSet S := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr (hN.preimage hf)
  change volume S=0
  rw [Measure.volume_eq_prod,Measure.prod_apply_symm hS]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro c
  by_cases hc : c∈I
  · obtain ⟨J,hJ,hJnull⟩ := hinv c hc
    apply measure_mono_null (t := J '' (N∩range f)) _ (hJnull _ inter_subset_right (measure_mono_null inter_subset_left hNz))
    rintro t ⟨a,ha,he⟩
    have h1 : (a : ℝ×ℝ).2=c := congrArg Prod.snd he
    have h2 : (a : ℝ×ℝ).1=t := congrArg Prod.fst he
    exact ⟨f a,⟨ha,⟨a,rfl⟩⟩,(hJ a h1).trans h2⟩
  · apply measure_mono_null (t := ∅) _ (measure_empty)
    rintro t ⟨a,ha,he⟩
    have he' : (a : ℝ×ℝ).2=c := congrArg Prod.snd he
    exact (hc (he' ▸ hwithin a)).elim

end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem ae_constant_of_product_rows_columns {A B Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {α : Measure A} {β : Measure B}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {P : A×B → Prop} (hP : ∀ᵐ p ∂α.prod β,P p) {F : A×B → Y}
    (hrow : ∀ a b b',P (a,b) → P (a,b') → F (a,b)=F (a,b'))
    (hcol : ∀ a a' b,P (a,b) → P (a',b) → F (a,b)=F (a',b)) :
    ∃ c : Y, ∀ᵐ p ∂α.prod β,F p=c := by
  have hp : ∀ᵐ a ∂α,∀ᵐ b ∂β,P (a,b) := ae_ae_of_ae_prod hP
  obtain ⟨a₀,ha₀⟩ := hp.exists
  obtain ⟨b₀,hb₀⟩ := ha₀.exists
  refine ⟨F (a₀,b₀),?_⟩
  have hrowc : ∀ᵐ a ∂α,∀ b,P (a,b) → F (a,b)=F (a₀,b₀) := by
    filter_upwards [hp] with a ha
    obtain ⟨b',hab',ha₀b'⟩ := (ha.and ha₀).exists
    intro b hab
    exact (hrow a b b' hab hab').trans ((hcol a a₀ b' hab' ha₀b').trans (hrow a₀ b' b₀ ha₀b' hb₀))
  have hr : ∀ᵐ p ∂α.prod β,∀ b,P (p.1,b) → F (p.1,b)=F (a₀,b₀) :=
    (measurePreserving_fst (μ := α) (ν := β)).quasiMeasurePreserving.ae hrowc
  filter_upwards [hP,hr] with p hp' hr'
  exact hr' p.2 hp'

theorem positive_atom_of_hopf_product {A B X Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    {α : Measure A} {β : Measure B} {μ : Measure X}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {π : A×B → X} (hπ : QuasiMeasurePreserving π (α.prod β) μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ,P x) {F : X → Y}
    (hrow : ∀ a b b',P (π (a,b)) → P (π (a,b')) → F (π (a,b))=F (π (a,b')))
    (hcol : ∀ a a' b,P (π (a,b)) → P (π (a',b)) → F (π (a,b))=F (π (a',b))) :
    ∃ c : Y,0<μ {x | F x=c} := by
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns (F := fun p => F (π p)) (hπ.ae hP) hrow hcol
  refine ⟨c,?_⟩
  by_contra hn
  have hn' : μ {x | F x=c}=0 := le_antisymm (not_lt.mp hn) (bot_le)
  have he : ∀ᵐ x ∂μ,F x≠c := by
    rw [ae_iff]
    simpa only [not_not] using hn'
  obtain ⟨p,hp,hp'⟩ := (hc.and (hπ.ae he)).exists
  exact hp' hp

end
end

end OAI
