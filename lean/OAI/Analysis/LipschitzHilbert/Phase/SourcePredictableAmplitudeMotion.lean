import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourceMovingWeights
import OAI.Analysis.LipschitzHilbert.Estimates.EndpointWeightBounds

namespace OAI

/-! The source's predictable amplitude estimate before absorbing the fixed
polynomial factors into the branching scale. The moving weights below are
the actual angular masses, including all shifted-boundary losses. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

/-- The per-top estimate retains four powers of the snapshot weight.
Only the unweighted interval estimate is an input; the weight motion is
derived from the physical geometry. -/
theorem source_single_top_predictable_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h start M : ℕ) (hstart : start ≤ M) (hbase : h ≤ start)
    (hgap : ∀ j, h ≤ j → j ≤ M → 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) M)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (phase : ℕ → ℂ) (a Z C : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    (hC : 1 ≤ C) (htC : (T top).weight Kw D z ≤ C)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff0 coeff1 : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (hmax : ∀ j, stop j ≤ M) (x0 y0 x1 y1 A E : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hinterval : ∀ l u, l ≤ u → u ≤ N →
      ‖P.rawInterval coeff0 jet l u x0 y0‖ ≤ A*((T top).weight Kw D z)^8)
    (hmotion : ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop j) →
      ‖P.rawInterval coeff1 jet l u x1 y1-U (P.rawInterval coeff0 jet l u x0 y0)‖ ≤
        E*((T top).weight Kw D z)^8) :
    let weight := fun t x => (T t).weight Kw D x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap Finset.univ (fun _ : Fin N => top) stop
        (fun j => P.rawBand coeff1 jet j x1 y1) phase a (SlopeBox.lineShift sR b z)
        start (g.index start (T top).slope)-
      U (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap Finset.univ (fun _ : Fin N => top) stop
        (fun j => P.rawBand coeff0 jet j x0 y0) phase a z
        start (g.index start (T top).slope))‖ ≤
      (V*((1+d)*E+d*A))*((T top).weight Kw D z)^4 := by
  dsimp only
  let weight := fun t x => (T t).weight Kw D x
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let n := fun x j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let m := fun x j => g.sourceBoundaryMass tops slope precision cutoff weight Kb gap j
    (g.index (j+1) (slope top)) x
  let z' := SlopeBox.lineShift sR b z
  let v0 := segmentWeight (n z) (boundaryLog (n z) (m z)) phase a start
  let v1 := segmentWeight (n z') (boundaryLog (n z') (m z')) phase a start
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
  let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
  let q := weight top z
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hweight (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  have hq : 0 < q := hweight top z
  have hn (j : ℕ) (hj : j ≤ M) : q ≤ n z j := by
    apply Finset.single_le_sum (fun t _ => (hweight t z).le)
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
      ⟨htop,rfl,g.eligible_of_le (hp top htop) hj he⟩
  have hv0 : ‖v0 M‖+(∑ j ∈ Finset.Ico start M, ‖v0 (j+1)-v0 j‖) ≤ V*q^(-(4:ℝ)) :=
    boundary_weight_variation_fourth (n z) (m z) phase start M Kb a q
      (∑ t ∈ tops, weight t z) C Z ha0 ha1 hq hZ hC htC hn
      (g.mass_le_total tops slope precision cutoff weight (fun t x => (hweight t x).le) 0 _ z)
      ((g.path_mass_antitone tops slope precision cutoff weight hp
        (fun t x => (hweight t x).le) top z).antitoneOn _)
      (fun j _ => g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun t x => (hweight t x).le) hKb gap j (slope top) z) hz0 hz
  have hvd : ‖v1 M-v0 M‖+(∑ j ∈ Finset.Ico start M,
      ‖(v1 (j+1)-v0 (j+1))-(v1 j-v0 j)‖) ≤ (d*V)*q^(-(4:ℝ)) := by
    have hv := g.source_moving_weight_variation tops T w B Kw D hw hB hKw hD hwidth
      hKb gap h start M hstart hbase hgap top htop he sR hs child hchild hblock b hb z
      phase a Z C ha0 ha1 hZ hz0 hz hC htC
    convert hv using 1
    dsimp [v0,v1,n,m,z',d,V,δ,q,weight,slope,precision,cutoff]
    ring
  have hv1 : ‖v1 M‖+(∑ j ∈ Finset.Ico start M, ‖v1 (j+1)-v1 j‖) ≤
      ((1+d)*V)*q^(-(4:ℝ)) := by
    calc
      _ ≤ (‖v0 M‖+(∑ j ∈ Finset.Ico start M, ‖v0 (j+1)-v0 j‖))+
          (‖v1 M-v0 M‖+(∑ j ∈ Finset.Ico start M,
            ‖(v1 (j+1)-v0 (j+1))-(v1 j-v0 j)‖)) := endpoint_variation_le_add v0 v1 start M
      _ ≤ V*q^(-(4:ℝ))+(d*V)*q^(-(4:ℝ)) := add_le_add hv0 hvd
      _ = _ := by ring
  have hbnd := g.sourcePacketAmplitude_single_top_motion tops slope precision cutoff weight
    hp hweight hKb gap phase M top htop he a z z' P coeff0 coeff1 jet stop hstop
    start hstart hmax x0 y0 x1 y1 (((1+d)*V)*q^(-(4:ℝ))) ((d*V)*q^(-(4:ℝ)))
    (A*q^8) (E*q^8) U (by positivity) (by positivity) hinterval hmotion hv1 hvd
  have hcancel : q^(-(4:ℝ))*q^8 = q^4 := by
    rw [← Real.rpow_natCast q 8, ← Real.rpow_add hq]
    norm_num
  calc
    _ ≤ (((1+d)*V)*q^(-(4:ℝ)))*(E*q^8)+((d*V)*q^(-(4:ℝ)))*(A*q^8) := hbnd
    _ = (V*((1+d)*E+d*A))*(q^(-(4:ℝ))*q^8) := by ring
    _ = _ := by rw [hcancel]

/-- The complete family of actual packets has motion proportional to
the mass of its angular node, independently of the number of tops. -/
theorem source_node_predictable_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h start : ℕ) (hbase : h ≤ start) (M : ι → ℕ)
    (hM : ∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t))
    (hMmax : ∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t)
    (hgap : ∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h)
    (sR : ℝ) (cell : ℤ) (hs : ∀ t ∈ g.cellTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) start cell,
      g.index h (T t).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (phase : ℕ → ℂ) (a Z C : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re)
    (hz : ∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z)
    (hC : 1 ≤ C) (htC : ∀ t ∈ tops, (T t).weight Kw D z ≤ C)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : ι → SourceLabeledLattice N κ Label Item)
    (coeff0 coeff1 : ∀ t j (l : (P t).labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : ι → Fin N → ℕ)
    (hstop : ∀ t ∈ tops, Antitone (stop t)) (hmax : ∀ t ∈ tops, ∀ j, stop t j ≤ M t)
    (x0 y0 x1 y1 : ι → ℝ) (A E : ℝ)
    (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hinterval : ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N →
      ‖(P t).rawInterval (coeff0 t) jet l u (x0 t) (y0 t)‖ ≤ A*((T t).weight Kw D z)^8)
    (hmotion : ∀ t ∈ g.cellTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) start cell,
      ∀ l u, l ≤ u → u ≤ N →
      (∀ j : Fin N, l ≤ j.val → j.val < u → start ≤ stop t j) →
      ‖(P t).rawInterval (coeff1 t) jet l u (x1 t) (y1 t)-
        U ((P t).rawInterval (coeff0 t) jet l u (x0 t) (y0 t))‖ ≤
        E*((T t).weight Kw D z)^8) :
    let weight := fun t x => (T t).weight Kw D x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2)
        (fun p => (P p.1).rawBand (coeff1 p.1) jet p.2 (x1 p.1) (y1 p.1))
        phase a (SlopeBox.lineShift sR b z) start cell-
      U (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2)
        (fun p => (P p.1).rawBand (coeff0 p.1) jet p.2 (x0 p.1) (y0 p.1))
        phase a z start cell)‖ ≤
      (V*((1+d)*E+d*A)*C^3)*g.mass tops (fun t => (T t).slope)
        (fun t => w/(T t).length) (g.rootWidth/B^2) weight start cell z := by
  dsimp only
  let weight := fun t x => (T t).weight Kw D x
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
  let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hd : 0 ≤ d := by
    have he := Real.one_le_exp (show 0 ≤ 2*δ by positivity)
    dsimp [d]
    positivity
  apply g.sourcePacketAmplitude_node_motion tops (fun t => (T t).slope)
    (fun t => w/(T t).length) (g.rootWidth/B^2) weight
    (fun t _ => (div_pos hw (T t).length_pos).le) Kb gap Finset.univ stop
    (fun t j => (P t).rawBand (coeff0 t) jet j (x0 t) (y0 t))
    (fun t j => (P t).rawBand (coeff1 t) jet j (x1 t) (y1 t))
    (fun t ht j _ => g.eligible_of_le (div_pos hw (T t).length_pos).le
      (hmax t ht j) (hM t ht)) phase a z (SlopeBox.lineShift sR b z) start cell U
    (V*((1+d)*E+d*A)) C (by dsimp [V]; positivity)
    (fun t _ => ((T t).weight_pos hKw D z).le)
    (fun t ht => htC t ((g.mem_cellTops _ _ _ _ _ _ _).mp ht).1)
  intro t ht
  obtain ⟨htt,_,hel⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
  exact g.source_single_top_predictable_motion tops T w B Kw D hw hB hKw hD hwidth
    hKb gap h start (M t) (hMmax t htt start hel) hbase (hgap t htt) t htt (hM t htt)
    sR (hs t ht) child hchild hblock b hb z phase a Z C ha0 ha1 hZ
    (hz0 t htt) (hz t htt) hC (htC t htt) (P t) (coeff0 t) (coeff1 t) jet
    (stop t) (hstop t htt) (hmax t htt) (x0 t) (y0 t) (x1 t) (y1 t) A E U
    hA hE (hinterval t htt) (hmotion t ht)

end LipschitzHilbert.AngularGrid

end

end OAI
