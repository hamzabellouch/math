import OAI.Analysis.CircleDomains.Rigidity.TraceCompression

namespace OAI

/-! Interval payment kills the compressed trace on a null subset of a
line. Countable local covers and tail compression then recover the full
uncompressed trace, including noninjective compressions. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem real_null_image_of_interval_payment
    (κ : Measure ℝ) [IsFiniteMeasure κ] [κ.OuterRegular]
    {C V : Set ℝ} (hV : IsOpen V) (hC : κ (C ∩ V) = 0) (v : ℝ → ℝ)
    (hpay : ∀ x ∈ C ∩ V, ∀ y ∈ C ∩ V, x ≤ y → Icc x y ⊆ V →
      |v y-v x| ≤ κ.real (Icc x y)) : volume (v '' (C ∩ V)) = 0 := by
  apply null_image_inter_open_of_connected_open_oscillation hV hC v zero_le_one
  intro U hUV _ hU x hx y hy
  have hforward (x : ℝ) (hx : x ∈ C ∩ U) (y : ℝ) (hy : y ∈ C ∩ U) (hxy : x ≤ y) :
      |v y-v x| ≤ κ.real U := by
    have hi : Icc x y ⊆ U := hU.isPreconnected.ordConnected.out hx.2 hy.2
    exact (hpay x ⟨hx.1,hUV hx.2⟩ y ⟨hy.1,hUV hy.2⟩ hxy (hi.trans hUV)).trans
      (measureReal_mono hi)
  rw [one_mul]
  rcases le_total x y with h | h
  · simpa only [abs_sub_comm] using hforward x hx y hy h
  · exact hforward y hy x hx h

 theorem null_image_of_local_null_image
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {C : Set X} {v : X → ℝ}
    (hlocal : ∀ x ∈ C, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ volume (v '' (C ∩ V)) = 0) :
    volume (v '' C) = 0 := by
  classical
  choose V hV hxV hn using (fun x : C => hlocal x x.property)
  obtain ⟨S,hSc,hS⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  let : Countable S := hSc.to_subtype
  have hc : v '' C ⊆ ⋃ x : S, v '' (C ∩ V x.val) := by
    rintro _ ⟨x,hx,rfl⟩
    have hxc : x ∈ ⋃ i ∈ S, V i := by rw [hS]; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxc
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,x,⟨hx,hxi⟩,rfl⟩
  exact measure_mono_null hc (measure_iUnion_null (fun x : S => hn x.val))

 theorem compression_comparison {X : Type*} (F : X → ℝ → ℝ) (b : X → ℝ)
    (H : ℝ → ℝ) (hH : Monotone H) {x y : X} {c : ℝ}
    (hinc : ∀ z s t, s ≤ t → H t-H s ≤ F z t-F z s)
    (hvar : ∀ t, |F x t-F y t| ≤ c) :
    |H (b x)-H (b y)| ≤ |F x (b x)-F y (b y)|+c := by
  rcases le_total (b x) (b y) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (hH h))]
    have hi := hinc x (b x) (b y) h
    have hv := (le_abs_self (F x (b y)-F y (b y))).trans (hvar (b y))
    have hu := neg_le_abs (F x (b x)-F y (b y))
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (hH h))]
    have hi := hinc y (b y) (b x) h
    have hv := (neg_le_abs (F x (b x)-F y (b x))).trans (hvar (b x))
    have hu := le_abs_self (F x (b x)-F y (b y))
    linarith

end CircleDomainRigidity

end

end OAI
