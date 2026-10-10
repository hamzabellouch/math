import Mathlib

namespace OAI

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

lemma usc_mul {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hf0 : ∀ x,0≤f x) (hg0 : ∀ x,0≤g x) :
    UpperSemicontinuous (fun x => f x*g x) := by
  intro x b hb
  have hc : Continuous (fun r : ℝ => (f x+r)*(g x+r)) := by fun_prop
  have hn : {r : ℝ | (f x+r)*(g x+r)<b}∈𝓝 0 := by
    exact hc.continuousAt.preimage_mem_nhds (x:=0) (t:=Iio b) (isOpen_Iio.mem_nhds (by simpa using hb))
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hn
  have hd' : (f x+δ/2)*(g x+δ/2)<b := hd (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)];linarith)
  filter_upwards [hf x (f x+δ/2) (by linarith),hg x (g x+δ/2) (by linarith)] with y hyf hyg
  exact (mul_le_mul hyf.le hyg.le (hg0 y) (by linarith [hf0 x])).trans_lt hd'

lemma usc_sqrt {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : UpperSemicontinuous f) : UpperSemicontinuous (fun x => Real.sqrt (f x)) :=
  Real.continuous_sqrt.comp_upperSemicontinuous hf (fun _ _ hab => Real.sqrt_le_sqrt hab)

lemma usc_indicator {X : Type*} [TopologicalSpace X] {f : X → ℝ} {S : Set X}
    (hf : UpperSemicontinuous f) (hf0 : ∀ x,0≤f x) (hS : IsClosed S) :
    UpperSemicontinuous (S.indicator f) := by
  have hh := usc_mul (hS.upperSemicontinuous_indicator (show (0:ℝ)≤1 by norm_num)) hf
    (fun x => by by_cases hx : x∈S <;> simp [hx]) hf0
  have he : (fun x => S.indicator (fun _ => (1:ℝ)) x * f x)=S.indicator f := by
    funext x
    by_cases hx : x∈S <;> simp [hx]
  rw [he] at hh
  exact hh

lemma usc_sup_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X × Y → ℝ} {K : Set Y} (hK : IsCompact K)
    (hF : UpperSemicontinuous F) :
    UpperSemicontinuous (fun x => sSup ((fun y => F (x,y)) '' K)) := by
  by_cases hne : K.Nonempty
  swap
  · have hk : K=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hk,Set.image_empty]
    exact upperSemicontinuous_const
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply upperSemicontinuous_iff_isClosed_preimage.2
  intro b
  have hc : IsClosed {p : X × K | b≤F (p.1,p.2)} := by
    exact (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).isClosed_preimage b
  have he : {x | b≤ sSup ((fun y => F (x,y)) '' K)}=
      Prod.fst '' {p : X × K | b≤F (p.1,p.2)} := by
    ext x
    constructor
    · intro hx
      have hu : UpperSemicontinuousOn (fun y => F (x,y)) K :=
        (hF.comp (continuous_const.prodMk continuous_id)).upperSemicontinuousOn K
      obtain ⟨y,hy,hm⟩ := hu.exists_isMaxOn hne hK
      have hsup : sSup ((fun y => F (x,y)) '' K)≤F (x,y) :=
        csSup_le (hne.image _) (by rintro _ ⟨z,hz,rfl⟩;exact hm hz)
      exact ⟨(x,⟨y,hy⟩),hx.trans hsup,rfl⟩
    · rintro ⟨⟨x',y⟩,hy,hx⟩
      change x'=x at hx
      subst x'
      exact hy.trans (le_csSup
        ((hF.comp (continuous_const.prodMk continuous_id)).upperSemicontinuousOn K |>.bddAbove_of_isCompact hK)
        (mem_image_of_mem _ y.property))
  change IsClosed {x | b≤ sSup ((fun y => F (x,y)) '' K)}
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

end Overlap

end

end OAI
