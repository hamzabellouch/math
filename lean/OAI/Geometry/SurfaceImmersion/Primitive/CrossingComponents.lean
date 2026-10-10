import OAI.Geometry.SurfaceImmersion.Geometry.OrderedBoundaryInvariant

namespace OAI

/-! Exact scalar identities used in the later-curve crossing calculation. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

/-- The normal components forced by the Gauss identity when the transverse
second-form component is `(S,0)`. -/
def frameXX (S D N L k : ℝ) : ℝ × ℝ := ((k+D^2+N^2)/S,L)
def frameXY (D N : ℝ) : ℝ × ℝ := (D,N)
def frameYY (S : ℝ) : ℝ × ℝ := (S,0)

def pureComponents (S D N L k b c : ℝ) : ℝ × ℝ :=
  b^2 • frameXX S D N L k + (2*b*c) • frameXY D N + c^2 • frameYY S

def slopePure (S D N L k t : ℝ) : ℝ × ℝ :=
  ((N^2+k+(D+S*t)^2)/S,L+2*N*t)

def slopeMixed (S D N L k t u : ℝ) : ℝ × ℝ :=
  ((N^2+k+(D+S*t)*(D+S*u))/S,L+N*(t+u))

lemma frame_gauss {S D N L k : ℝ} (hS : S ≠ 0) :
    (frameXX S D N L k).1*S-((frameXY D N).1^2+(frameXY D N).2^2) = k := by
  dsimp [frameXX,frameXY]
  field_simp; ring

lemma pure_first_identity {S D N L k b c : ℝ} (hS : S ≠ 0) :
    S*(pureComponents S D N L k b c).1 = (D*b+S*c)^2+(k+N^2)*b^2 := by
  dsimp [pureComponents,frameXX,frameXY,frameYY]
  field_simp; ring

lemma pure_second_identity (S D N L k b c : ℝ) :
    (pureComponents S D N L k b c).2 = L*b^2+2*N*b*c := by
  simp only [pureComponents,frameXX,frameXY,frameYY,Prod.snd_add,
    Prod.smul_snd,smul_eq_mul]
  ring

lemma pure_unit_slope {S D N L k t : ℝ} (hS : S ≠ 0) :
    pureComponents S D N L k 1 t = slopePure S D N L k t := by
  ext <;> dsimp [pureComponents,frameXX,frameXY,frameYY,slopePure] <;> field_simp <;> ring

lemma mixed_sub_left {S D N L k t u : ℝ} (hS : S ≠ 0) :
    slopeMixed S D N L k t u-slopePure S D N L k t =
      (u-t) • (D+S*t,N) := by
  ext <;> dsimp [slopeMixed,slopePure] <;> field_simp <;> ring

lemma mixed_sub_right {S D N L k t u : ℝ} (hS : S ≠ 0) :
    slopeMixed S D N L k t u-slopePure S D N L k u =
      (t-u) • (D+S*u,N) := by
  ext <;> dsimp [slopeMixed,slopePure] <;> field_simp <;> ring

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
