import OAI.Analysis.StrictMeans.DiscreteLaplacian

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma scalar_floor_mesh {A s : ℝ} (hA : 0≤A) (hs : 0<s) :
    s*(⌊A/s⌋₊:ℝ)≤A ∧ A-s<s*(⌊A/s⌋₊:ℝ) := by
  constructor
  · exact by simpa only [mul_comm] using (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hA hs.le))
  · have h := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (A/s))
    nlinarith

lemma meshPoint_mem_latticeBox {o : ℂ} {s : ℝ} (hs : 0<s) {N M : ℕ} {v : Lattice} :
    v∈latticeBox N M ↔ |(meshPoint o s v).re-o.re|≤ s*N ∧ |(meshPoint o s v).im-o.im|≤ s*M := by
  rw [meshPoint_re,meshPoint_im,add_sub_cancel_left,add_sub_cancel_left,
    abs_mul,abs_mul,abs_of_pos hs,mul_le_mul_iff_right₀ hs,mul_le_mul_iff_right₀ hs]
  change (|(ofLex v).1|≤(N:ℤ) ∧ |(ofLex v).2|≤(M:ℤ)) ↔ _
  constructor <;> intro h <;> constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2
  · exact_mod_cast h.1
  · exact_mod_cast h.2

lemma meshBox_in_rectangle {o : ℂ} {s A B : ℝ} (hs : 0<s) (hA : 0≤A) (hB : 0≤B)
    {v : Lattice} (hv : v∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊) :
    meshPoint o s v∈planeRectangle o A B := by
  have h := (meshPoint_mem_latticeBox (o:=o) hs).mp hv
  exact ⟨h.1.trans (scalar_floor_mesh hA hs).1,h.2.trans (scalar_floor_mesh hB hs).1⟩

lemma meshBox_contains_star {o : ℂ} {s A B δ : ℝ} (hs : 0<s) (hA : 0≤A) (hB : 0≤B)
    (hsmall : 3*s<δ) {v : Lattice}
    (hv : |(meshPoint o s v).re-o.re|+δ≤A ∧ |(meshPoint o s v).im-o.im|+δ≤B)
    {w : Lattice} (hw : w∈meshStar ex ey v) : w∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊ := by
  apply (meshPoint_mem_latticeBox (o:=o) hs).mpr
  have hd := meshPoint_star_dist (o:=o) (s:=s) hw
  rw [abs_of_pos hs,dist_eq_norm] at hd
  have hx : |(meshPoint o s w).re-(meshPoint o s v).re|≤2*s :=
    (Complex.abs_re_le_norm ((meshPoint o s w)-(meshPoint o s v))).trans hd
  have hy : |(meshPoint o s w).im-(meshPoint o s v).im|≤2*s :=
    (Complex.abs_im_le_norm ((meshPoint o s w)-(meshPoint o s v))).trans hd
  have hxf := (scalar_floor_mesh hA hs).2
  have hyf := (scalar_floor_mesh hB hs).2
  constructor
  · have ht := abs_sub_le (meshPoint o s w).re (meshPoint o s v).re o.re
    linarith [hv.1]
  · have ht := abs_sub_le (meshPoint o s w).im (meshPoint o s v).im o.im
    linarith [hv.2]

lemma smooth_halfPlane_sublevel_index_lower {u : ℂ → ℝ} {c : ℝ}
    (hK : IsCompact {z : ℂ | 0<z.im ∧ u z≤c})
    (hne : (interior {z : ℂ | 0<z.im ∧ u z≤c}).Nonempty)
    (hu : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ 2 u z)
    (htr : ∀ z : ℂ, 0<z.im → 0<second u z 1 1+second u z Complex.I Complex.I) :
    ∃ o : ℂ, ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ S : Finset Lattice,
      (∀ v, v∈S ↔ 0<(meshPoint o s v).im ∧ u (meshPoint o s v)≤c) →
        1≤∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v := by
  classical
  let K : Set ℂ := {z | 0<z.im ∧ u z≤c}
  obtain ⟨o,A,B,δ,hA,hB,hδ,hmargin,hrect⟩ := compact_halfPlane_rectangle hK
    (hne.mono interior_subset) (fun z hz=>hz.1)
  have ha := compact_laplace_ascent (compact_planeRectangle o A B)
    (fun z hz=>hu z (hrect z hz)) (fun z hz=>htr z (hrect z hz))
  have hh := meshPoint_hits_interior hne o
  refine ⟨o,?_⟩
  filter_upwards [ha,hh,gt_mem_nhds (show (0:ℝ)<δ/3 by positivity)] with s hs hsample hsmall
  intro hspos S hS
  have hcontains (v : Lattice) (hv : meshPoint o s v∈K) (w : Lattice)
      (hw : w∈meshStar ex ey v) : w∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊ :=
    meshBox_contains_star hspos hA.le hB.le (by linarith) (hmargin _ hv) hw
  have hbox (v : Lattice) (hv : v∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊) : meshPoint o s v∈planeRectangle o A B :=
    meshBox_in_rectangle hspos hA.le hB.le hv
  have hS' (v : Lattice) : v∈S ↔ v∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊ ∧ (u ∘ meshPoint o s) v≤c := by
    constructor
    · intro hv
      have hv' := (hS v).mp hv
      exact ⟨hcontains v hv' v (mem_meshStar_self _ _ _),hv'.2⟩
    · intro hv
      exact (hS v).mpr ⟨hrect _ (hbox v hv.1),hv.2⟩
  apply box_sublevel_index (u:=u ∘ meshPoint o s) (c:=c) ?_ ?_ ?_ S hS'
  · obtain ⟨v,hv⟩ := hsample hspos
    exact ⟨v,hcontains v hv v (mem_meshStar_self _ _ _),hv.2⟩
  · intro v hv hvc w hw
    exact hcontains v ⟨hrect _ (hbox v hv),hvc⟩ w hw
  · intro v hv
    simpa only [Function.comp_apply,meshPoint_add,meshPoint_sub,latticeCoord_ex,latticeCoord_ey]
      using hs _ (hbox v hv) hspos

end
end StrictInverseFirstPower.Grid

end

end OAI
