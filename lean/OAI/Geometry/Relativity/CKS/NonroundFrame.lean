import OAI.Geometry.Relativity.CKS.AngularDifferentiation

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators Matrix
abbrev I := Fin 3
abbrev A := Fin 2

structure ConnectionData where
  B : A → ℝ
  rotation : ℝ
  chi11 : ℝ
  chi12 : ℝ
  chi22 : ℝ
  leaf : A → ℝ

def chi (c : ConnectionData) : Matrix A A ℝ :=
  !![c.chi11,c.chi12;c.chi12,c.chi22]

def leafConnection (c : ConnectionData) (a : A) : Matrix A A ℝ :=
  !![0,c.leaf a;-c.leaf a,0]

def connection (c : ConnectionData) : I → Matrix I I ℝ :=
  ![!![0,c.B 0,c.B 1; -c.B 0,0,c.rotation; -c.B 1,-c.rotation,0],
    !![0,c.chi11,c.chi12; -c.chi11,0,c.leaf 0; -c.chi12,-c.leaf 0,0],
    !![0,c.chi12,c.chi22; -c.chi12,0,c.leaf 1; -c.chi22,-c.leaf 1,0]]

lemma connection_metric (c : ConnectionData) (i j k : I) :
    connection c i j k = -connection c i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [connection]

lemma connection_normal (c : ConnectionData) (a b : A) :
    connection c a.succ 0 b.succ = chi c a b := by
  fin_cases a <;> fin_cases b <;> rfl

def curvature (c : ConnectionData) (dc : I → ConnectionData) (i j k l : I) : ℝ :=
  connection (dc i) j k l-connection (dc j) i k l+
  ∑ m, (connection c j k m*connection c i m l-
    connection c i k m*connection c j m l-
    (connection c i j m-connection c j i m)*connection c m k l)

def scalarCurvature (c : ConnectionData) (dc : I → ConnectionData) : ℝ :=
  ∑ i, ∑ j, curvature c dc i j j i

def leafCurvature (c : ConnectionData) (dc : I → ConnectionData) (a b d e : A) : ℝ :=
  leafConnection (dc a.succ) b d e-leafConnection (dc b.succ) a d e+
  ∑ m, (leafConnection c b d m*leafConnection c a m e-
    leafConnection c a d m*leafConnection c b m e-
    (leafConnection c a b m-leafConnection c b a m)*leafConnection c m d e)

def leafScalar (c : ConnectionData) (dc : I → ConnectionData) : ℝ :=
  ∑ a, ∑ b, leafCurvature c dc a b b a

def mean (c : ConnectionData) : ℝ := c.chi11+c.chi22

def normalMean (dc : I → ConnectionData) : ℝ := (dc 0).chi11+(dc 0).chi22

def chiNormSq (c : ConnectionData) : ℝ := c.chi11^2+2*c.chi12^2+c.chi22^2

def accelNormSq (c : ConnectionData) : ℝ := (c.B 0)^2+(c.B 1)^2

def accelDiv (c : ConnectionData) (dc : I → ConnectionData) : ℝ :=
  ∑ a, ((dc a.succ).B a+∑ b, leafConnection c a b a*c.B b)

lemma leafScalar_formula (c : ConnectionData) (dc : I → ConnectionData) :
    leafScalar c dc = 2*((dc 2).leaf 0-(dc 1).leaf 1-(c.leaf 0)^2-(c.leaf 1)^2) := by
  simp [leafScalar,leafCurvature,leafConnection,Fin.sum_univ_succ]
  ring

lemma scalarCurvature_formula (c : ConnectionData) (dc : I → ConnectionData) :
    scalarCurvature c dc = leafScalar c dc-2*normalMean dc-(mean c)^2-
      chiNormSq c+2*accelDiv c dc-2*accelNormSq c := by
  rw [leafScalar_formula]
  simp [scalarCurvature,curvature,connection,mean,normalMean,chiNormSq,accelDiv,
    accelNormSq,leafConnection,Fin.sum_univ_succ]
  ring

end
end CKSFrame

end

end OAI
