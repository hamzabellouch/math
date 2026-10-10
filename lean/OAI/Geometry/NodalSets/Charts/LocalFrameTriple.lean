import OAI.Geometry.NodalSets.Charts.FrameMapFamily
import OAI.Geometry.NodalSets.Elliptic.LocalDirectionTriple

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

structure AdmissibleFrameTriple
    (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : T → Coord) where
  q : T → Fin 3 → Coord
  continuous_q : Continuous q
  independent : ∀ t, LinearIndependent ℝ (q t)
  perpendicular : ∀ t j, g t (p t) (q t j) = 0
  length : ∀ t j, g t (q t j) (q t j) = g t (p t) (p t)+4
  strict : ∀ t j, 0 < H t (p t) (p t)+H t (q t j) (q t j)
  e : T → Fin 3 → Fin 4 → Coord
  continuous_e : ∀ j i, Continuous (fun t ↦ e t j i)
  orthonormal : ∀ t j i k, g t (e t j i) (e t j k) = if i=k then 1 else 0
  first : ∀ t j, e t j 0 = metricNormalize (g t) (p t)
  second : ∀ t j, e t j 1 = metricNormalize (g t) (q t j)

def AdmissibleFrameTriple.pullback {R : Type*} [TopologicalSpace R]
    {g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ} {p : T → Coord}
    (d : AdmissibleFrameTriple g H p) (f : R → T) (hf : Continuous f) :
    AdmissibleFrameTriple (g ∘ f) (H ∘ f) (p ∘ f) where
  q := d.q ∘ f
  continuous_q := d.continuous_q.comp hf
  independent r := d.independent (f r)
  perpendicular r := d.perpendicular (f r)
  length r := d.length (f r)
  strict r := d.strict (f r)
  e := d.e ∘ f
  continuous_e j i := (d.continuous_e j i).comp hf
  orthonormal r := d.orthonormal (f r)
  first r := d.first (f r)
  second r := d.second (f r)

theorem exists_local_frame_triple
    (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hs : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (t0 : T) (hdir : ∃ v : Coord, g t0 (p t0) v = 0 ∧ g t0 v v = 1 ∧
      0 < H t0 (p t0) (p t0)+(g t0 (p t0) (p t0)+4)*H t0 v v) :
    ∃ U : Set T, U ∈ 𝓝 t0 ∧ Nonempty
      (AdmissibleFrameTriple (fun t : U ↦ g t) (fun t : U ↦ H t) (fun t : U ↦ p t)) := by
  obtain ⟨v,hvp,hvv,hvH⟩ := hdir
  obtain ⟨q0,hqI,hq0,_⟩ := admissible_direction_triple (g t0) (H t0) (hpos t0)
    (hs t0) (p t0) v (hp0 t0) hvp hvv hvH
  obtain ⟨U,q,hU,hq,_,hprop⟩ := continue_admissible_triple g H hg hH hpos p hp hp0
    t0 q0 hqI (fun j ↦ (hq0 j).1) (fun j ↦ (hq0 j).2.1) (fun j ↦ (hq0 j).2.2)
  let u0 : U := ⟨t0,mem_of_mem_nhds hU⟩
  have hqc : Continuous (fun t : U ↦ q t) := continuousOn_iff_continuous_domRestrict.mp hq
  have hqne (t : U) (j : Fin 3) : q t j ≠ 0 := by
    intro hz
    have hh := ((hprop t t.property).2 j).2.1
    rw [hz] at hh
    have hhpos := hpos t (p t) (hp0 t)
    simp only [map_zero] at hh
    linarith
  have hex (j : Fin 3) := exists_continuous_adapted_frame
    (fun t : U ↦ g t) (hg.comp continuous_subtype_val) (fun t ↦ hs t)
    (fun t ↦ hpos t) (fun t : U ↦ p t) (fun t : U ↦ q t j)
    (hp.comp continuous_subtype_val) ((continuous_apply j).comp hqc)
    (fun t ↦ hp0 t) (fun t ↦ hqne t j) (fun t ↦ ((hprop t t.property).2 j).1) u0
  choose V e hV he haxes ho using hex
  let W : Set U := ⋂ j, V j
  have hW : W ∈ 𝓝 u0 := Filter.iInter_mem.mpr hV
  let D : Set T := Subtype.val '' W
  have hD : D ∈ 𝓝 t0 := by
    have hh := mem_nhds_subtype_iff_nhdsWithin.mp hW
    rwa [nhdsWithin_eq_nhds.mpr hU] at hh
  let f : D → U := fun t ↦ ⟨t,by obtain ⟨u,_,hu⟩ := t.property; simp [← hu]⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hfV (t : D) (j : Fin 3) : f t ∈ V j := by
    obtain ⟨u,hu,heq⟩ := t.property
    have hh : f t = u := Subtype.ext heq.symm
    rw [hh]
    exact mem_iInter.mp hu j
  refine ⟨D,hD,⟨{
    q := fun t ↦ q t
    continuous_q := hqc.comp hf
    independent := fun t ↦ (hprop t (f t).property).1
    perpendicular := fun t j ↦ ((hprop t (f t).property).2 j).1
    length := fun t j ↦ ((hprop t (f t).property).2 j).2.1
    strict := fun t j ↦ ((hprop t (f t).property).2 j).2.2
    e := fun t j ↦ e j (f t)
    continuous_e := ?_
    orthonormal := fun t j ↦ ho j (f t) (hfV t j)
    first := fun t j ↦ (haxes j (f t)).1
    second := fun t j ↦ (haxes j (f t)).2 }⟩⟩
  intro j i
  exact (he j i).comp_continuous hf (fun t ↦ hfV t j)

end
end Yau.Geometry

end OAI
