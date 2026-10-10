import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.CutEdges
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.GraphGeometry.UniformGeometry

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def heightCut (π : V → ℤ) (t : ℤ) : Set E := G.cutEdges {v | t < π v}

lemma finite_height_interval (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite)
    (a b : ℤ) : (π ⁻¹' Set.Icc a b).Finite := by
  have hh := (Set.finite_Icc a b).biUnion (fun t _ => hπ t)
  convert hh using 1
  ext v
  simp

lemma finite_heightCut (hlocal : G.LocallyFinite) (π : V → ℤ)
    (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ)) (t : ℤ) :
    (G.heightCut π t).Finite := by
  apply (G.finite_incident hlocal (finite_height_interval π hπ (t-J) t)).subset
  rintro e ⟨x,y,he,hx,hy⟩
  have hxy := (abs_le.mp (hJ e x y he)).1
  refine ⟨x,?_,?_⟩
  · change t-(J:ℤ) ≤ π x ∧ π x ≤ t
    change ¬t<π x at hx
    change t<π y at hy
    omega
  · simp [he]

lemma heightCut_disjoint (π : V → ℤ) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (t u : ℤ) (htu : (J:ℤ) ≤ |t-u|) :
    Disjoint (G.heightCut π t) (G.heightCut π u) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨x,y,he,hx,hy⟩ ⟨a,b,hef,ha,hb⟩
  change ¬t<π x at hx
  change t<π y at hy
  change ¬u<π a at ha
  change u<π b at hb
  have hj := abs_le.mp (hJ e x y he)
  rcases Sym2.eq_iff.mp (he.symm.trans hef) with ⟨hxa,hyb⟩|⟨hxb,hya⟩
  · subst a; subst b
    rcases le_total t u with hl|hl
    · rw [abs_of_nonpos (sub_nonpos.mpr hl)] at htu
      omega
    · rw [abs_of_nonneg (sub_nonneg.mpr hl)] at htu
      omega
  · subst b; subst a
    omega

lemma heightCut_translate (π : V → ℤ) (φ : G.Aut) (a : ℤ)
    (hφ : ∀ v, π (φ.vertex v)=π v+a) (t : ℤ) :
    φ.edge '' G.heightCut π t = G.heightCut π (t+a) := by
  ext e
  constructor
  · rintro ⟨f,⟨x,y,hf,hx,hy⟩,rfl⟩
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,?_⟩
    · rw [φ.preserves,hf,Sym2.map_mk]
    · change ¬t+a<π (φ.vertex x)
      rw [hφ]
      change ¬t<π x at hx
      omega
    · change t+a<π (φ.vertex y)
      rw [hφ]
      change t<π y at hy
      omega
  · rintro ⟨x,y,he,hx,hy⟩
    refine ⟨φ.edge.symm e,?_,φ.edge.apply_symm_apply e⟩
    refine ⟨φ.vertex.symm x,φ.vertex.symm y,?_,?_,?_⟩
    · have hh := (Aut.symm G φ).preserves e
      change G.ends (φ.edge.symm e) = s(φ.vertex.symm x,φ.vertex.symm y)
      change G.ends (φ.edge.symm e) = Sym2.map φ.vertex.symm (G.ends e) at hh
      rw [hh,he,Sym2.map_mk]
    · have hh := hφ (φ.vertex.symm x)
      simp only [Equiv.apply_symm_apply] at hh
      change ¬t<π (φ.vertex.symm x)
      change ¬t+a<π x at hx
      omega
    · have hh := hφ (φ.vertex.symm y)
      simp only [Equiv.apply_symm_apply] at hh
      change t<π (φ.vertex.symm y)
      change t+a<π y at hy
      omega

lemma heightCut_ncard (π : V → ℤ)
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t) (t : ℤ) :
    (G.heightCut π t).ncard = (G.heightCut π 0).ncard := by
  obtain ⟨φ,hφ⟩ := htrans t
  have he := G.heightCut_translate π φ t hφ 0
  simp only [zero_add] at he
  rw [← he,Set.ncard_image_of_injective _ φ.edge.injective]

lemma cluster_bounded_by_closed_cuts (π : V → ℤ) (ω : Set E) (a b : ℤ)
    (ha : Disjoint (G.heightCut π a) ω) (hb : Disjoint (G.heightCut π b) ω)
    (o : V) (hoa : a<π o) (hob : π o≤b) :
    G.cluster ω o ⊆ π ⁻¹' Set.Icc (a+1) b := by
  intro v hv
  constructor
  · by_contra h
    have hva : ¬a<π v := by change ¬a+1≤π v at h; omega
    exact G.not_reachable_of_cut_closed {v | a<π v} ω
      (fun e he => Set.disjoint_left.mp ha he) hva hoa hv.symm
  · by_contra h
    have hvb : b<π v := lt_of_not_ge h
    exact G.not_reachable_of_cut_closed {v | b<π v} ω
      (fun e he => Set.disjoint_left.mp hb he) (not_lt.mpr hob) hvb hv

end CriticalPercolation.BondGraph
end
end
end

end OAI
