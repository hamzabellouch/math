import Mathlib
import OAI.Combinatorics.HoneycombCorridor.ConvexCuts
import OAI.Combinatorics.HoneycombCorridor.RaySeparation

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def lostCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) : Finset (List Bool) :=
  sourceExits D bottomSource \ sourceExits (upperCut D k A) bottomSource

noncomputable def rightIndexMass (D : Finset Vertex) (A : ℤ) : ℝ :=
  positiveWordMass (lostCut D 1 A)

theorem phasedMass_constant_turn (S : Finset (List Bool)) (m : ℤ)
    (h : ∀ w ∈ S, turnUnits w = m) :
    phasedWordMass S = (positiveWordMass S : ℂ) * phase (Real.pi/8 * (m : ℝ)) := by
  simp only [phasedWordMass,positiveWordMass,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [wordWeight_turnUnits,h w hw,Complex.ofReal_pow]
  rfl

theorem lostCut_phases (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) :
    (∃ b : ℝ, 0 ≤ b ∧ phasedWordMass (lostCut D 1 A) = (b : ℂ)*phase (-Real.pi/4)) ∧
    (∃ a : ℝ, 0 ≤ a ∧ phasedWordMass (lostCut D 2 A) = (a : ℂ)*phase (-Real.pi/8)) := by
  have hflux (k : Fin 3) : phasedWordMass (lostCut D k A) =
      phasedWordMass (sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :=
    flux_subtraction D _ bottomSource (admissiblyConvex_filled D hD)
      (admissiblyConvex_filled _ (upperCut_convex D hD k A)) hg'
      (fun hm => hg' (upperCut_subset D k A hm))
  constructor
  · refine ⟨positiveWordMass (sourceExits (upperCut D 1 A) bottomSource \ sourceExits D bottomSource),
      positiveWordMass_nonneg _,?_⟩
    rw [hflux 1,phasedMass_constant_turn _ (-2) (fun w hw =>
      (new_upperCut_turn D hD hg hg' A hA 1 w hw).1 rfl)]
    congr 2
    push_cast
    ring
  · refine ⟨positiveWordMass (sourceExits (upperCut D 2 A) bottomSource \ sourceExits D bottomSource),
      positiveWordMass_nonneg _,?_⟩
    rw [hflux 2,phasedMass_constant_turn _ (-1) (fun w hw =>
      (new_upperCut_turn D hD hg hg' A hA 2 w hw).2 rfl)]
    congr 2
    push_cast
    ring

theorem strip_index_bounds (h : ℕ) (v : Vertex) (hv : InStrip h v) :
    boxIndex v 1 ≤ boxIndex v 2 ∧ boxIndex v 2 ≤ boxIndex v 1 + (h : ℤ) := by
  cases v <;> simp [InStrip,boxIndex] at * <;> omega

theorem position_index (v : Vertex) :
    (position v).1 = ((boxIndex v 1 : ℝ) + (boxIndex v 2 : ℝ)) / 2 := by
  cases v <;> simp [position,boxIndex] <;> ring

theorem lostCut_nested (h : ℕ) (D : Finset Vertex) (hstrip : ∀ v ∈ D, InStrip h v)
    (A : ℤ) : lostCut D 1 A ⊆ lostCut D 2 A ∧ lostCut D 2 A ⊆ lostCut D 1 (A-h) := by
  have hm (k : Fin 3) (B : ℤ) (w : List Bool) : w ∈ lostCut D k B ↔
      w ∈ sourceExits D bottomSource ∧ ∃ v ∈ traced bottomSource w, B ≤ boxIndex v k :=
    mem_lost_upperCut D bottomSource k B w
  constructor
  · intro w hw
    obtain ⟨he,v,hv,hA⟩ := (hm 1 A w).mp hw
    have hd := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := strip_index_bounds h v (hstrip v hd)
    exact (hm 2 A w).mpr ⟨he,v,hv,by omega⟩
  · intro w hw
    obtain ⟨he,v,hv,hA⟩ := (hm 2 A w).mp hw
    have hd := (stopped_traced D bottomSource w ((mem_sourceExits _ _ _).mp he).1).2 v hv
    have hi := strip_index_bounds h v (hstrip v hd)
    exact (hm 1 (A-h) w).mpr ⟨he,v,hv,by omega⟩

theorem lostCut_real_lower (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (k : Fin 3) (A : ℤ) :
    Real.cos (3*Real.pi/8)*positiveWordMass (lostCut D k A) ≤
      (phasedWordMass (lostCut D k A)).re := by
  rw [phasedWordMass,Complex.re_sum,positiveWordMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have he := (Finset.mem_sdiff.mp hw).1
  exact convex_wordWeight_re_lower D hD (bottomSource,w)
    ⟨hg,hg',(mem_sourceExits _ _ _).mp he⟩

theorem rightIndexMass_step (h : ℕ) (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hstrip : ∀ v ∈ D, InStrip h v)
    (A : ℤ) (hA : 0 < A) :
    rightIndexMass D A ≤ rayContraction * rightIndexMass D (A-h) := by
  have hout := bottomSource_outside_of_strip h D hstrip
  obtain ⟨⟨b,hb,hb'⟩,⟨a,_,ha'⟩⟩ := lostCut_phases D hD hg hout A hA
  have hn := lostCut_nested h D hstrip A
  have hc := separated_rays_contract (lostCut D 2 A) (lostCut D 1 A) hn.1
    (lostCut_real_lower D hD hg hout 1 A) a b hb ha' hb'
  exact hc.trans (mul_le_mul_of_nonneg_left (positiveWordMass_mono hn.2) rayContraction_range.1.le)

theorem rightIndexMass_total_bound (h : ℕ) (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hstrip : ∀ v ∈ D, InStrip h v) (A : ℤ) :
    rightIndexMass D A ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  apply (positiveWordMass_mono (show lostCut D 1 A ⊆ sourceExits D bottomSource from
    Finset.sdiff_subset)).trans
  exact boundary_source_weight_bound D bottomSource hD hg (bottomSource_outside_of_strip h D hstrip)

theorem rightIndexMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightIndexMass D ((n : ℤ)*h) ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by
  induction n with
  | zero => simpa using rightIndexMass_total_bound h D hD hg hstrip 0
  | succ n ih =>
    have hA : 0 < ((n+1 : ℕ) : ℤ)*(h : ℤ) := by positivity
    have hs := rightIndexMass_step h D hD hg hstrip _ hA
    have hi : ((n+1 : ℕ) : ℤ)*(h : ℤ) - h = (n : ℤ)*h := by push_cast; ring
    rw [hi] at hs
    calc
      _ ≤ rayContraction * rightIndexMass D ((n : ℤ)*h) := hs
      _ ≤ rayContraction * ((Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n) :=
        mul_le_mul_of_nonneg_left ih rayContraction_range.1.le
      _ = _ := by rw [pow_succ]; ring

end PolynomialVacuumBridge.Corridor

end

end OAI
